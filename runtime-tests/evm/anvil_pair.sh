#!/usr/bin/env bash
# Engineering Anvil gate for the Lean-surface Pair bytecode.
# Multi-slot: constructor writes left only; initBoth writes both;
# creditLeft keeps right. Missing anvil/cast → skip (exit 0), not pass.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

foundry_bin="${FOUNDRY_BIN:-$HOME/.foundry/bin}"
anvil="$foundry_bin/anvil"
cast="$foundry_bin/cast"
port="${SOLANA_LEAN_EVM_PORT:-18548}"
chain_id="${SOLANA_LEAN_EVM_CHAIN_ID:-31338}"
rpc="http://127.0.0.1:$port"
private_key="${SOLANA_LEAN_EVM_PRIVATE_KEY:-ac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"
log="$root/build/evm/anvil-pair.log"
UINT64_MAX="18446744073709551615"

die() {
  echo "evm-anvil-pair: FAIL: $*" >&2
  exit 1
}

skip() {
  echo "evm-anvil-pair: skip: $*" >&2
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

require_pair() {
  local addr="$1" left="$2" right="$3" label="$4"
  require_uint_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'getLeft()(uint64)')" \
    "$left" "$label getLeft"
  require_uint_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'getRight()(uint64)')" \
    "$right" "$label getRight"
  require_storage_uint "$addr" 0 "$left" "$label storage left"
  require_storage_uint "$addr" 1 "$right" "$label storage right"
}

bin="$root/build/evm/Pair.bin"
if [[ ! -f "$bin" ]]; then
  echo "evm-anvil-pair: assembling Pair.bin" >&2
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
[[ -n "$bytecode" ]] || die "empty Pair.bin"

encoded="$("$cast" abi-encode 'constructor(uint64)' 7)"
receipt="$("$cast" send --json --rpc-url "$rpc" --private-key "$private_key" \
  --create "0x${bytecode}${encoded#0x}")"
addr="$(/usr/bin/python3 -I -S -c \
  'import json,sys; print(json.load(sys.stdin)["contractAddress"])' <<<"$receipt")"

# 1. constructor writes left; right stays zero (fresh storage)
require_pair "$addr" 7 0 "constructor"

# 2. initBoth writes both slots
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'initBoth(uint64,uint64)' 5 99 >/dev/null
require_pair "$addr" 5 99 "initBoth"

# 3. eth_call creditLeft does not commit
simulated="$("$cast" call --rpc-url "$rpc" "$addr" 'creditLeft(uint64)(uint64)' 3)"
require_uint_equal "$simulated" "8" "creditLeft return"
require_pair "$addr" 5 99 "eth_call creditLeft must not commit"

# 4. send creditLeft updates left only
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'creditLeft(uint64)' 3 >/dev/null
require_pair "$addr" 8 99 "creditLeft"

# 5. overflow holds both slots
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'initBoth(uint64,uint64)' "$UINT64_MAX" 99 >/dev/null
require_pair "$addr" "$UINT64_MAX" 99 "max left"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'creditLeft(uint64)' 1 >/dev/null 2>&1; then
  die "overflow creditLeft unexpectedly succeeded"
fi
require_pair "$addr" "$UINT64_MAX" 99 "overflow hold"

echo "evm-anvil-pair: ok (ctor/initBoth/creditLeft/right-hold; engineering only)"
