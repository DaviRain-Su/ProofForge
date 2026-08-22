#!/usr/bin/env bash
# Engineering Anvil gate for the Lean-surface Counter bytecode.
# Aligns with PF smoke_evm.sh StateCell matrix and Mollusk Counter 4/4.
# Not bytecode refinement. Missing anvil/cast → skip (exit 0), not pass.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

foundry_bin="${FOUNDRY_BIN:-$HOME/.foundry/bin}"
anvil="$foundry_bin/anvil"
cast="$foundry_bin/cast"
port="${SOLANA_LEAN_EVM_PORT:-18547}"
chain_id="${SOLANA_LEAN_EVM_CHAIN_ID:-31338}"
rpc="http://127.0.0.1:$port"
# Anvil default account 0.
private_key="${SOLANA_LEAN_EVM_PRIVATE_KEY:-ac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"
log="$root/build/evm/anvil-counter.log"
UINT64_MAX="18446744073709551615"

die() {
  echo "evm-anvil-counter: FAIL: $*" >&2
  exit 1
}

skip() {
  echo "evm-anvil-counter: skip: $*" >&2
  exit 0
}

for tool in "$anvil" "$cast"; do
  if [[ ! -x "$tool" ]]; then
    skip "missing $tool"
  fi
done

require_equal() {
  local actual="$1" expected="$2" message="$3"
  [[ "$actual" == "$expected" ]] || die "$message (expected '$expected', got '$actual')"
}

to_dec() {
  local x="$1"
  x="${x//$'\n'/}"
  x="${x%%[*}"
  x="${x// /}"
  if [[ -z "$x" ]]; then
    echo ""
    return
  fi
  if [[ "$x" == 0x* || "$x" == 0X* ]]; then
    /usr/bin/python3 -I -S -c "print(int('$x', 16))"
  elif [[ "$x" =~ ^[0-9]+$ ]]; then
    echo "$x"
  else
    echo "$x"
  fi
}

require_uint_equal() {
  local actual="$1" expected="$2" message="$3"
  local canonical
  canonical="$(to_dec "$actual")"
  require_equal "$canonical" "$expected" "$message (raw='$actual')"
}

require_storage_uint() {
  local addr="$1" slot="$2" expected="$3" message="$4"
  local raw actual
  raw="$("$cast" storage --rpc-url "$rpc" "$addr" "$slot")"
  actual="$(to_dec "$raw")"
  require_equal "$actual" "$expected" "$message (storage slot $slot raw=$raw)"
}

require_revert_preserves_slot0() {
  local addr="$1"
  local expected_slot="$2"
  local label="$3"
  shift 3
  if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
      "$addr" "$@" >/dev/null 2>&1; then
    die "$label: overflow/revert transaction unexpectedly succeeded"
  fi
  require_storage_uint "$addr" 0 "$expected_slot" \
    "$label: overflow must leave storage slot 0 unchanged"
}

bin="$root/build/evm/Counter.bin"
if [[ ! -f "$bin" ]]; then
  echo "evm-anvil-counter: assembling Counter.bin" >&2
  lake exe evmLeanAssemble -- "$root/build/evm" >/dev/null \
    || die "lake exe evmLeanAssemble failed"
fi
[[ -f "$bin" ]] || die "missing $bin"

if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then
  die "RPC endpoint $rpc is already occupied"
fi

mkdir -p "$root/build/evm"
"$anvil" --host 127.0.0.1 --port "$port" --chain-id "$chain_id" \
  --silent >"$log" 2>&1 &
anvil_pid=$!
cleanup() {
  kill "$anvil_pid" 2>/dev/null || true
  wait "$anvil_pid" 2>/dev/null || true
}
trap cleanup EXIT

ready=0
for _ in $(seq 1 50); do
  if ! kill -0 "$anvil_pid" 2>/dev/null; then
    die "anvil exited before readiness; see $log"
  fi
  if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then
    ready=1
    break
  fi
  sleep 0.1
done
[[ "$ready" == 1 ]] || die "anvil failed to start; see $log"
require_equal "$("$cast" chain-id --rpc-url "$rpc")" "$chain_id" \
  "launched Anvil chain identity mismatch"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || die "empty Counter.bin"

deploy() {
  local initial="$1"
  local encoded receipt
  encoded="$("$cast" abi-encode 'constructor(uint64)' "$initial")"
  receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
    --create "0x${bytecode}${encoded#0x}")"
  /usr/bin/python3 -I -S -c \
    'import json,sys; print(json.load(sys.stdin)["contractAddress"])' <<<"$receipt"
}

# 1. constructor writes slot 0; view + storage dual-read
addr="$(deploy 7)"
before="$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')"
require_uint_equal "$before" "7" "constructor state mismatch (view)"
require_storage_uint "$addr" 0 "7" "constructor state mismatch (storage)"

# 2. eth_call increment returns next value and does not commit
simulated="$("$cast" call --rpc-url "$rpc" "$addr" 'increment(uint64)(uint64)' 5)"
require_uint_equal "$simulated" "12" "increment return mismatch"
require_uint_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')" "7" \
  "eth_call increment unexpectedly committed state"

# 3. nonpayable: value on increment / constructor must fail
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 2 \
    "$addr" 'increment(uint64)' 5 >/dev/null 2>&1; then
  die "nonpayable increment unexpectedly accepted value"
fi
encoded7="$("$cast" abi-encode 'constructor(uint64)' 7)"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" --value 1 --create \
    "0x${bytecode}${encoded7#0x}" >/dev/null 2>&1; then
  die "nonpayable constructor unexpectedly accepted value"
fi

# 4. send increment commits; view + storage
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'increment(uint64)' 5 >/dev/null
after="$("$cast" call --rpc-url "$rpc" "$addr" 'get()(uint64)')"
require_uint_equal "$after" "12" "increment state mismatch (view)"
require_storage_uint "$addr" 0 "12" "increment state mismatch (storage)"
balance="$("$cast" balance --rpc-url "$rpc" "$addr")"
require_equal "$(to_dec "$balance")" "0" "contract accepted native value"

# 5. overflow reverts and holds
max_addr="$(deploy "$UINT64_MAX")"
require_storage_uint "$max_addr" 0 "$UINT64_MAX" "max constructor storage"
require_revert_preserves_slot0 "$max_addr" "$UINT64_MAX" "overflow" \
  'increment(uint64)' 1
require_uint_equal "$("$cast" call --rpc-url "$rpc" "$max_addr" 'get()(uint64)')" \
  "$UINT64_MAX" "overflow changed view state"

echo "evm-anvil-counter: ok (ctor/get/increment/overflow hold; engineering only)"
