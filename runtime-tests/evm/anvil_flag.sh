#!/usr/bin/env bash
# Flag: UInt8 flag in slot 0 (masked), UInt64 count in slot 1.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

foundry_bin="${FOUNDRY_BIN:-$HOME/.foundry/bin}"
anvil="$foundry_bin/anvil"
cast="$foundry_bin/cast"
port="${SOLANA_LEAN_EVM_PORT:-18549}"
chain_id="${SOLANA_LEAN_EVM_CHAIN_ID:-31338}"
rpc="http://127.0.0.1:$port"
private_key="${SOLANA_LEAN_EVM_PRIVATE_KEY:-ac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"
log="$root/build/evm/anvil-flag.log"

die() { echo "evm-anvil-flag: FAIL: $*" >&2; exit 1; }
skip() { echo "evm-anvil-flag: skip: $*" >&2; exit 0; }

for tool in "$anvil" "$cast"; do
  [[ -x "$tool" ]] || skip "missing $tool"
done

require_equal() {
  [[ "$1" == "$2" ]] || die "$3 (expected '$2', got '$1')"
}

to_dec() {
  local x="$1"
  x="${x//$'\n'/}"; x="${x%%[*]}"; x="${x// /}"
  if [[ "$x" == 0x* || "$x" == 0X* ]]; then
    /usr/bin/python3 -I -S -c "print(int('$x', 16))"
  else
    echo "$x"
  fi
}

require_uint() {
  require_equal "$(to_dec "$1")" "$2" "$3"
}

require_storage() {
  require_uint "$("$cast" storage --rpc-url "$rpc" "$1" "$2")" "$3" "$4"
}

bin="$root/build/evm/Flag.bin"
if [[ ! -f "$bin" ]]; then
  lake exe evmLeanAssemble -- "$root/build/evm" >/dev/null || die "assemble failed"
fi
[[ -f "$bin" ]] || die "missing $bin"

if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then
  die "RPC $rpc occupied"
fi

mkdir -p "$root/build/evm"
"$anvil" --host 127.0.0.1 --port "$port" --chain-id "$chain_id" --silent >"$log" 2>&1 &
anvil_pid=$!
cleanup() { kill "$anvil_pid" 2>/dev/null || true; wait "$anvil_pid" 2>/dev/null || true; }
trap cleanup EXIT

ready=0
for _ in $(seq 1 50); do
  kill -0 "$anvil_pid" 2>/dev/null || die "anvil died; see $log"
  if "$cast" chain-id --rpc-url "$rpc" >/dev/null 2>&1; then ready=1; break; fi
  sleep 0.1
done
[[ "$ready" == 1 ]] || die "anvil failed to start"

bytecode="$(tr -d '\n\r ' < "$bin")"
encoded="$("$cast" abi-encode 'constructor(uint64)' 7)"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  --create "0x${bytecode}${encoded#0x}")"
addr="$(/usr/bin/python3 -I -S -c \
  'import json,sys; print(json.load(sys.stdin)["contractAddress"])' <<<"$receipt")"

require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" 0 "ctor getFlag"
require_storage "$addr" 0 0 "ctor flag slot"
require_storage "$addr" 1 7 "ctor count slot"

"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setFlag(uint64)' 1 >/dev/null
require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'getFlag()(uint64)')" 1 "setFlag view"
require_storage "$addr" 0 1 "setFlag flag"
require_storage "$addr" 1 7 "setFlag keeps count"

if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'setFlag(uint64)' 256 >/dev/null 2>&1; then
  die "setFlag(256) should revert"
fi
require_storage "$addr" 0 1 "overflow holds flag"
require_storage "$addr" 1 7 "overflow holds count"

echo "evm-anvil-flag: ok (u8 mask + count hold; engineering only)"
