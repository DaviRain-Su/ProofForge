---
id: wsm-near-storage-balance-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-output-001, wsm-near-storage-registration-001]
---

# wsm-near-storage-balance-output-001 bounded optional StorageBalance JSON output

## Objective

Add the exact output prerequisite for a later `storage_balance_of`-shaped view without exposing a
public NEP-145 method or choosing fixed versus variable-account registration economics.

## Delivered

- Compiler-owned `StorageBalanceResult` has exactly five source leaves: presence, total `(w0,w1)`,
  and available `(w0,w1)`. Only that nominal schema selects
  `near-json-storage-balance-option-v1`; ordinary records do not.
- View-only target lowering emits `null` for absent with mandatory zero inactive limbs, or exact
  declaration-order `{"total":"<u128>","available":"<u128>"}` for present. Presence above one,
  malformed frame size, mutation, and Promise combination fail closed.
- The emitter reuses one decimal helper, a 39-byte scratch span, and an exact 105-byte maximum
  object arena. Each runtime branch invokes `value_return` exactly once.
- Structural and real nearcore scenes pin absent, present zero, 2^64, 2^64+1, asymmetric limbs,
  max/max, malformed presence/inactive data, and repeated-call stale isolation.

## Boundary

The bytes match current near-sdk `Option<StorageBalance>` output. This slice does not export
`storage_balance_of`, calculate a registration cost, expose storage bounds, or claim NEP-145 ABI
compatibility. ProofForge's closed registration policy still measures actual variable AccountId
key deltas; this serializer intentionally makes no economic-policy decision.
