# Shared Anvil helpers for Darwin and Linux.
# Source after `set -euo pipefail`. Sets: root, anvil, cast, python, chain_id, private_key.
# Missing tools → skip (exit 0), not pass. Unsupported OS → skip.

solana_lean_evm_root() {
  local here
  here="$(cd "$(dirname "${BASH_SOURCE[1]}")" && pwd)"
  (cd "$here/../.." && pwd)
}

solana_lean_python() {
  if command -v python3 >/dev/null 2>&1; then
    echo python3
  elif command -v python >/dev/null 2>&1; then
    echo python
  else
    return 1
  fi
}

# Prefer FOUNDRY_BIN, then ~/.foundry/bin (foundryup on macOS and Linux), then PATH.
solana_lean_find_tool() {
  local name="$1"
  local dir candidate
  if [[ -n "${FOUNDRY_BIN:-}" ]]; then
    candidate="${FOUNDRY_BIN%/}/$name"
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  fi
  if [[ -n "${HOME:-}" ]]; then
    candidate="$HOME/.foundry/bin/$name"
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  fi
  if command -v "$name" >/dev/null 2>&1; then
    command -v "$name"
    return 0
  fi
  for dir in /usr/local/bin /opt/homebrew/bin /usr/bin; do
    candidate="$dir/$name"
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  done
  return 1
}

solana_lean_evm_init() {
  local label="${1:-evm-anvil}"
  case "$(uname -s)" in
    Darwin|Linux) ;;
    *)
      echo "$label: skip: unsupported host $(uname -s) (want Darwin or Linux)" >&2
      exit 0
      ;;
  esac
  root="$(solana_lean_evm_root)"
  cd "$root"
  python="$(solana_lean_python)" || {
    echo "$label: skip: python3/python not found" >&2
    exit 0
  }
  anvil="$(solana_lean_find_tool anvil)" || {
    echo "$label: skip: anvil not found (install foundryup, or set FOUNDRY_BIN)" >&2
    exit 0
  }
  cast="$(solana_lean_find_tool cast)" || {
    echo "$label: skip: cast not found (install foundryup, or set FOUNDRY_BIN)" >&2
    exit 0
  }
  chain_id="${PF_EVM_CHAIN_ID:-31338}"
  # Anvil default account 0.
  private_key="${PF_EVM_PRIVATE_KEY:-ac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"
}

solana_lean_to_dec() {
  local x="$1"
  x="${x//$'\n'/}"
  x="${x%%[*}"
  x="${x// /}"
  if [[ -z "$x" ]]; then
    echo ""
    return
  fi
  if [[ "$x" == 0x* || "$x" == 0X* ]]; then
    "$python" -I -S -c "print(int('$x', 16))"
  else
    echo "$x"
  fi
}

solana_lean_require_equal() {
  local actual="$1" expected="$2" message="$3"
  [[ "$actual" == "$expected" ]] || {
    echo "FAIL: $message (expected '$expected', got '$actual')" >&2
    exit 1
  }
}

solana_lean_require_uint() {
  local raw="$1" expected="$2" message="$3"
  solana_lean_require_equal "$(solana_lean_to_dec "$raw")" "$expected" "$message (raw='$raw')"
}

solana_lean_require_storage() {
  local addr="$1" slot="$2" expected="$3" message="$4"
  local raw
  raw="$("$cast" storage --rpc-url "$rpc" "$addr" "$slot")"
  solana_lean_require_uint "$raw" "$expected" "$message (slot $slot)"
}

# Anvil-only corruption probe: replace one full storage word so fail-closed malformed-state paths
# can be exercised. Production/deployment scripts never call this helper.
solana_lean_set_storage_word() {
  local addr="$1" slot="$2" value="$3"
  local slot_word value_word
  slot_word="$("$python" -I -S -c "print(f'0x{int(\"$slot\"):064x}')")"
  value_word="$("$python" -I -S -c "print(f'0x{int(\"$value\"):064x}')")"
  "$cast" rpc --rpc-url "$rpc" anvil_setStorageAt \
    "$addr" "$slot_word" "$value_word" >/dev/null
}

solana_lean_contract_address() {
  "$python" -I -S -c 'import json,sys; print(json.load(sys.stdin)["contractAddress"])'
}

solana_lean_ensure_bin() {
  local path="$1"
  if [[ ! -f "$path" ]]; then
    echo "assembling $path" >&2
    lake exe pfEvmAssemble -- "$root/build/evm" >/dev/null \
      || { echo "FAIL: lake exe pfEvmAssemble failed" >&2; exit 1; }
  fi
  [[ -f "$path" ]] || { echo "FAIL: missing $path" >&2; exit 1; }
}

# Start anvil on $port. Sets rpc, anvil_pid. Traps cleanup.
solana_lean_start_anvil() {
  local port="$1"
  local log="$2"
  rpc="http://127.0.0.1:$port"
  if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then
    echo "FAIL: RPC endpoint $rpc is already occupied" >&2
    exit 1
  fi
  mkdir -p "$(dirname "$log")"
  "$anvil" --host 127.0.0.1 --port "$port" --chain-id "$chain_id" \
    --silent >"$log" 2>&1 &
  anvil_pid=$!
  cleanup() {
    kill "$anvil_pid" 2>/dev/null || true
    wait "$anvil_pid" 2>/dev/null || true
  }
  trap cleanup EXIT
  local ready=0 i
  for i in $(seq 1 50); do
    if ! kill -0 "$anvil_pid" 2>/dev/null; then
      echo "FAIL: anvil exited before readiness; see $log" >&2
      exit 1
    fi
    if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then
      ready=1
      break
    fi
    sleep 0.1
  done
  [[ "$ready" == 1 ]] || { echo "FAIL: anvil failed to start; see $log" >&2; exit 1; }
  solana_lean_require_equal "$("$cast" chain-id --rpc-url "$rpc")" "$chain_id" \
    "launched Anvil chain identity mismatch"
}

solana_lean_deploy_ctor_u64() {
  local bytecode="$1"
  local initial="$2"
  local encoded receipt
  encoded="$("$cast" abi-encode 'constructor(uint64)' "$initial")"
  receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
    --create "0x${bytecode}${encoded#0x}")"
  printf '%s' "$receipt" | solana_lean_contract_address
}

solana_lean_deploy_ctor_u64x3() {
  local bytecode="$1"
  local a="$2"
  local b="$3"
  local c="$4"
  local encoded receipt
  encoded="$("$cast" abi-encode 'constructor(uint64,uint64,uint64)' "$a" "$b" "$c")"
  receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
    --create "0x${bytecode}${encoded#0x}")"
  printf '%s' "$receipt" | solana_lean_contract_address
}

# eth_call must revert with ABI error Insufficient(uint256,uint256).
solana_lean_require_insufficient() {
  local addr="$1" from="$2" data="$3" have="$4" want="$5" message="$6"
  local sel
  sel="$("$cast" keccak 'Insufficient(uint256,uint256)')"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8+64+64 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing Insufficient(have,want) (got '+repr(err)+' result='+repr(resp.get('result'))+')')
have=int(blob[8:72], 16)
want=int(blob[72:136], 16)
if have != int('$have') or want != int('$want'):
    raise SystemExit(f'FAIL: $message: Insufficient({have},{want}) != ($have,$want)')
"
}

# eth_call must revert with ABI error Unauthorized(address).
solana_lean_require_unauthorized() {
  local addr="$1" from="$2" data="$3" who="$4" message="$5"
  local sel
  sel="$("$cast" keccak 'Unauthorized(address)')"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  who="$(printf '%s' "$who" | tr 'A-Z' 'a-z')"
  who="${who#0x}"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8+64 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing Unauthorized(who) (got '+repr(err)+')')
got=blob[8+24:8+64]
if got != '$who':
    raise SystemExit(f'FAIL: $message: Unauthorized(0x{got}) != 0x$who')
"
}

# eth_call must revert with the ABI error of the given signature (e.g. 'oob()'), no arguments.
solana_lean_require_named_revert() {
  local addr="$1" from="$2" data="$3" signature="$4" message="$5"
  local sel
  sel="$("$cast" keccak "$signature")"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing $signature revert (got '+repr(err)+')')
"
}

# eth_call must revert with the exact selector and ordered ABI uint words supplied after message.
solana_lean_require_word_revert() {
  local addr="$1" from="$2" data="$3" signature="$4" message="$5"
  shift 5
  local sel
  sel="$("$cast" keccak "$signature")"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S - "$rpc" "$addr" "$from" "$data" "$sel" "$signature" "$message" "$@" <<'PY'
import json, sys, urllib.error, urllib.request

rpc, addr, sender, data, selector, signature, message, *words = sys.argv[1:]
payload = {
    "jsonrpc": "2.0",
    "id": 1,
    "method": "eth_call",
    "params": [{"to": addr, "from": sender, "data": data}, "latest"],
}
request = urllib.request.Request(
    rpc,
    data=json.dumps(payload).encode(),
    headers={"Content-Type": "application/json"},
)
try:
    raw = urllib.request.urlopen(request).read().decode()
except urllib.error.HTTPError as error:
    raw = error.read().decode()
response = json.loads(raw)
failure = response.get("error") or {}
blob = failure.get("data") or ""
if isinstance(blob, dict):
    blob = blob.get("data") or blob.get("raw") or ""
blob = str(blob).lower().removeprefix("0x")
expected = selector + "".join(f"{int(word, 0):064x}" for word in words)
if blob != expected:
    raise SystemExit(
        f"FAIL: {message}: {signature} returndata {blob!r} != {expected!r} "
        f"(error={failure!r})"
    )
PY
}

# eth_call must revert with ABI error CapExceeded().
solana_lean_require_cap_exceeded() {
  local addr="$1" from="$2" data="$3" message="$4"
  local sel
  sel="$("$cast" keccak 'CapExceeded()')"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing CapExceeded() (got '+repr(err)+')')
"
}

# eth_call must revert with ABI error Paused().
solana_lean_require_paused() {
  local addr="$1" from="$2" data="$3" message="$4"
  local sel
  sel="$("$cast" keccak 'Paused()')"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing Paused() (got '+repr(err)+')')
"
}

# eth_call must revert with ABI error ZeroAddress().
solana_lean_require_zero_address() {
  local addr="$1" from="$2" data="$3" message="$4"
  local sel
  sel="$("$cast" keccak 'ZeroAddress()')"
  sel="${sel#0x}"
  sel="$(printf '%s' "$sel" | cut -c1-8 | tr 'A-Z' 'a-z')"
  "$python" -I -S -c "
import json, urllib.request, urllib.error
rpc='$rpc'
payload={
  'jsonrpc':'2.0','id':1,'method':'eth_call',
  'params':[{'to':'$addr','from':'$from','data':'$data'}, 'latest']
}
req=urllib.request.Request(rpc, data=json.dumps(payload).encode(),
  headers={'Content-Type':'application/json'})
try:
    raw=urllib.request.urlopen(req).read().decode()
except urllib.error.HTTPError as e:
    raw=e.read().decode()
resp=json.loads(raw)
err=resp.get('error') or {}
blob=(err.get('data') or '')
if isinstance(blob, dict):
    blob=blob.get('data') or blob.get('raw') or ''
blob=str(blob).lower()
if blob.startswith('0x'):
    blob=blob[2:]
sel='$sel'
if len(blob) < 8 or not blob.startswith(sel):
    raise SystemExit('FAIL: $message: missing ZeroAddress() (got '+repr(err)+')')
"
}

solana_lean_deploy_ctor_address() {
  local bytecode="$1"
  local addr="$2"
  local encoded receipt
  encoded="$("$cast" abi-encode 'constructor(address)' "$addr")"
  receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
    --create "0x${bytecode}${encoded#0x}")"
  printf '%s' "$receipt" | solana_lean_contract_address
}
