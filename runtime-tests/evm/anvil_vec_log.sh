#!/usr/bin/env bash
# EvmVecLog: owner-gated bounded UInt64 audit log over the StorageVec persistent vector policy
# (capacity 4). Covers push-to-full, CapExceeded, active-prefix reads, OOB amend, unauthorized
# access, clear, and documented stale-slot behavior.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil-vec-log
bin="$root/build/evm/EvmVecLog.bin"
solana_lean_ensure_bin "$bin"
solana_lean_start_anvil "${PF_EVM_PORT:-18572}" "$root/build/evm/anvil-vec-log.log"

bytecode="$(tr -d '\n\r ' < "$bin")"
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
solana_lean_require_storage "$addr" 0 "$admin_w0" "constructor admin.w0"
solana_lean_require_storage "$addr" 1 "$admin_w1" "constructor admin.w1"
solana_lean_require_storage "$addr" 2 "$admin_w2" "constructor admin.w2"
for slot in 3 4 5 6 7; do
  solana_lean_require_storage "$addr" "$slot" 0 "constructor zero entry/count slot"
done
solana_lean_require_equal "$("$cast" call --rpc-url "$rpc" "$addr" 'adminOf()(address)')" \
  "$sender" "admin getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'countOf()(uint64)')" 0 \
  "empty count getter"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'entryAt(uint64)(uint64)' 0)" 0 "active-prefix read on empty log is the 0 fallback"

other_key="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
other="$("$cast" wallet address --private-key "$other_key")"

# Non-admin record reverts Unauthorized(other) and cannot append.
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'record(uint64)' 1)" "$other" "non-admin record"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'record(uint64)' 1 >/dev/null 2>&1; then
  echo "FAIL: non-admin record unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 0 "unauthorized record holds count"

# Admin appends fill the active prefix in order.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'record(uint64)' 11 >/dev/null
solana_lean_require_storage "$addr" 3 11 "record writes entries[0]"
solana_lean_require_storage "$addr" 7 1 "record bumps count"
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'record(uint64)' 22 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'record(uint64)' 33 >/dev/null
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'record(uint64)' 44 >/dev/null
solana_lean_require_storage "$addr" 4 22 "record writes entries[1]"
solana_lean_require_storage "$addr" 5 33 "record writes entries[2]"
solana_lean_require_storage "$addr" 6 44 "record writes entries[3]"
solana_lean_require_storage "$addr" 7 4 "full log count"
for i in 0 1 2 3; do
  solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
    'entryAt(uint64)(uint64)' "$i")" "$(( (i + 1) * 11 ))" "active-prefix read $i"
done
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'entryAt(uint64)(uint64)' 4)" 0 "OOB read is the 0 fallback on a full log"

# Full log rejects the fifth record with CapExceeded() and stores nothing.
solana_lean_require_cap_exceeded "$addr" "$sender" \
  "$("$cast" calldata 'record(uint64)' 55)" "full log record"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'record(uint64)' 55 >/dev/null 2>&1; then
  echo "FAIL: full-log record unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 4 "full record holds count"
solana_lean_require_storage "$addr" 3 11 "full record holds entries[0]"

# Amend rewrites exactly one active slot; neighbors hold.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" \
  "$addr" 'amend(uint64,uint64)' 1 99 >/dev/null
solana_lean_require_storage "$addr" 4 99 "amend writes entries[1]"
solana_lean_require_storage "$addr" 3 11 "amend holds entries[0]"
solana_lean_require_storage "$addr" 5 33 "amend holds entries[2]"
solana_lean_require_storage "$addr" 7 4 "amend holds count"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'entryAt(uint64)(uint64)' 1)" 99 "amended read"

# OOB amend (index = count) reverts with the typed oob() error and stores nothing.
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'amend(uint64,uint64)' 4 5)" 'oob()' "OOB amend"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'amend(uint64,uint64)' 4 5 >/dev/null 2>&1; then
  echo "FAIL: OOB amend unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 4 99 "OOB amend holds entries[1]"
solana_lean_require_storage "$addr" 7 4 "OOB amend holds count"

# Non-admin amend and wipe revert Unauthorized(other).
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'amend(uint64,uint64)' 0 5)" "$other" "non-admin amend"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'amend(uint64,uint64)' 0 5 >/dev/null 2>&1; then
  echo "FAIL: non-admin amend unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_unauthorized "$addr" "$other" \
  "$("$cast" calldata 'wipe()')" "$other" "non-admin wipe"
if "$cast" send --rpc-url "$rpc" --private-key "$other_key" \
    "$addr" 'wipe()' >/dev/null 2>&1; then
  echo "FAIL: non-admin wipe unexpectedly succeeded" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 4 "unauthorized wipe holds count"

# Wipe resets only the length: backing slots keep their stale values and entryAt falls back.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'wipe()' >/dev/null
solana_lean_require_storage "$addr" 7 0 "wipe clears count"
solana_lean_require_storage "$addr" 3 11 "wipe leaves stale entries[0] unreachable"
solana_lean_require_storage "$addr" 4 99 "wipe leaves stale entries[1] unreachable"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'entryAt(uint64)(uint64)' 0)" 0 "wiped read is the 0 fallback despite the stale slot"
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" 'countOf()(uint64)')" 0 \
  "wiped count getter"

# The log accepts new records after a wipe and overwrites the stale prefix.
"$cast" send --rpc-url "$rpc" --private-key "$private_key" "$addr" 'record(uint64)' 55 >/dev/null
solana_lean_require_storage "$addr" 3 55 "post-wipe record overwrites entries[0]"
solana_lean_require_storage "$addr" 4 99 "post-wipe record leaves stale entries[1] unreachable"
solana_lean_require_storage "$addr" 7 1 "post-wipe count"

# Inject an impossible count and prove every mutation fails with malformed() before any store.
solana_lean_set_storage_word "$addr" 7 5
solana_lean_require_uint "$("$cast" call --rpc-url "$rpc" "$addr" \
  'entryAt(uint64)(uint64)' 0)" 0 "malformed count closes active-prefix reads"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'record(uint64)' 66)" 'malformed()' "malformed record"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'amend(uint64,uint64)' 0 66)" 'malformed()' "malformed amend"
solana_lean_require_named_revert "$addr" "$sender" \
  "$("$cast" calldata 'wipe()')" 'malformed()' "malformed wipe"
if "$cast" send --rpc-url "$rpc" --private-key "$private_key" \
    "$addr" 'wipe()' >/dev/null 2>&1; then
  echo "FAIL: malformed wipe unexpectedly repaired count" >&2
  exit 1
fi
solana_lean_require_storage "$addr" 7 5 "malformed mutations hold count"
solana_lean_require_storage "$addr" 3 55 "malformed mutations hold entries[0]"

echo "evm-anvil-vec-log: ok (bounded log push/set/clear + full/OOB/malformed/unauthorized + stale slots; engineering only)"
