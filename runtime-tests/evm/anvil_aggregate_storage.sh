#!/usr/bin/env bash
# EvmAggregateStorage: nested Bundle/Details static layout (Feature A depth ≤ 2).
# Covers constructor admin limbs, admin-gated nested writes, sibling-leaf preservation,
# leaf views, flat product (bundleSignal), nested product views (bundleView/detailsView),
# and Unauthorized(non-admin).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-aggregate-storage
bin="$root/build/evm/EvmAggregateStorage.bin"
if [[ ! -f "$bin" ]]; then
  echo "building registered EvmAggregateStorage.bin" >&2
  lake build Examples.Evm.EvmAggregateStorage >/dev/null \
    || { echo "FAIL: lake build Examples.Evm.EvmAggregateStorage failed" >&2; exit 1; }
  lake exe pf -- build --target evm --out "$root/build/evm" EvmAggregateStorage >/dev/null \
    || { echo "FAIL: build registered EvmAggregateStorage failed" >&2; exit 1; }
fi
[[ -f "$bin" ]] || { echo "FAIL: missing $bin" >&2; exit 1; }
solana_lean_start_anvil "${PF_EVM_PORT:-18567}" "$root/build/evm/anvil-aggregate-storage.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
[[ -n "$bytecode" ]] || { echo "FAIL: empty EvmAggregateStorage.bin" >&2; exit 1; }

sender="$("$cast" wallet address --private-key "$private_key")"
addr="$(solana_lean_deploy_ctor_address "$bytecode" "$sender")"

admin_words="$("$python" -I -S -c "
b=bytes.fromhex('${sender#0x}')
print(int.from_bytes(b[0:8], 'little'), int.from_bytes(b[8:16], 'little'),
      int.from_bytes(b[16:20], 'little'))
")"
admin_w0="${admin_words%% *}"
rest="${admin_words#* }"
admin_w1="${rest%% *}"
admin_w2="${rest#* }"

# Slots 0..5: admin_w0..w2, bundle_amount, bundle_details_side, bundle_details_enabled.
solana_lean_require_storage "$addr" 0 "$admin_w0" "constructor admin.w0"
solana_lean_require_storage "$addr" 1 "$admin_w1" "constructor admin.w1"
solana_lean_require_storage "$addr" 2 "$admin_w2" "constructor admin.w2"
for slot in 3 4 5; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero bundle leaf"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'adminOf()(address)')" \
  "$sender" "admin getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'amountOf()(uint64)')" \
  0 "constructor amount view"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sideOf()(uint8)')" \
  0 "constructor side view"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'enabledOf()(bool)')" \
  false "constructor enabled view"
signal0="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleSignal()(uint64,bool)')"
signal0_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$signal0''')))")"
solana_lean_require_equal "$signal0_values" "0 false" "constructor bundleSignal"
view0="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleView()(uint64,(uint8,bool))')"
view0_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$view0''')))")"
solana_lean_require_equal "$view0_values" "0 0 false" "constructor bundleView"
details0="$("$cast" call --rpc-url "$rpc" "$addr" 'detailsView()(uint8,bool)')"
details0_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$details0''')))")"
solana_lean_require_equal "$details0_values" "0 false" "constructor detailsView"

# Full nested write: amount + details.side + details.enabled in one admin call.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setBundle(uint64,uint8,bool)' 11 4 true >/dev/null
solana_lean_require_storage "$addr" 3 11 "setBundle amount"
solana_lean_require_storage "$addr" 4 4 "setBundle details.side"
solana_lean_require_storage "$addr" 5 1 "setBundle details.enabled"
solana_lean_require_storage "$addr" 0 "$admin_w0" "setBundle holds admin.w0"
solana_lean_require_storage "$addr" 1 "$admin_w1" "setBundle holds admin.w1"
solana_lean_require_storage "$addr" 2 "$admin_w2" "setBundle holds admin.w2"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'amountOf()(uint64)')" \
  11 "amountOf after setBundle"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'sideOf()(uint8)')" \
  4 "sideOf after setBundle"
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'enabledOf()(bool)')" \
  true "enabledOf after setBundle"
signal1="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleSignal()(uint64,bool)')"
signal1_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$signal1''')))")"
solana_lean_require_equal "$signal1_values" "11 true" "bundleSignal after setBundle"
view1="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleView()(uint64,(uint8,bool))')"
view1_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$view1''')))")"
solana_lean_require_equal "$view1_values" "11 4 true" "bundleView after setBundle"
details1="$("$cast" call --rpc-url "$rpc" "$addr" 'detailsView()(uint8,bool)')"
details1_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$details1''')))")"
solana_lean_require_equal "$details1_values" "4 true" "detailsView after setBundle"

# Targeted amount update must preserve nested details sibling leaves.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'setAmount(uint64)' 42 >/dev/null
solana_lean_require_storage "$addr" 3 42 "setAmount amount"
solana_lean_require_storage "$addr" 4 4 "setAmount holds details.side"
solana_lean_require_storage "$addr" 5 1 "setAmount holds details.enabled"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'amountOf()(uint64)')" \
  42 "amountOf after setAmount"
signal2="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleSignal()(uint64,bool)')"
signal2_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$signal2''')))")"
solana_lean_require_equal "$signal2_values" "42 true" "bundleSignal after setAmount"
view2="$("$cast" call --rpc-url "$rpc" "$addr" 'bundleView()(uint64,(uint8,bool))')"
view2_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$view2''')))")"
solana_lean_require_equal "$view2_values" "42 4 true" "bundleView after setAmount"
details2="$("$cast" call --rpc-url "$rpc" "$addr" 'detailsView()(uint8,bool)')"
details2_values="$("$python" -I -S -c "import re; print(' '.join(re.findall(r'[0-9]+|true|false', '''$details2''')))")"
solana_lean_require_equal "$details2_values" "4 true" "detailsView after setAmount"

# Non-admin nested write reverts Unauthorized(other) and cannot mutate leaves.
other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setBundle(uint64,uint8,bool)' 9 2 false)" "$other" \
  "non-admin setBundle"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setBundle(uint64,uint8,bool)' 9 2 false >/dev/null 2>&1; then
  echo "FAIL: non-admin setBundle unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 42 "unauthorized setBundle holds amount"
solana_lean_require_storage "$addr" 4 4 "unauthorized setBundle holds side"
solana_lean_require_storage "$addr" 5 1 "unauthorized setBundle holds enabled"

solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'setAmount(uint64)' 1)" "$other" "non-admin setAmount"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'setAmount(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-admin setAmount unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 3 42 "unauthorized setAmount holds amount"

echo "evm-anvil-aggregate-storage: ok (nested Bundle/Details slots + leaf/nested product views + admin gates; engineering only)"
