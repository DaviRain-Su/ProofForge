---
id: wsm-near-json-boolean-mutation-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-storage-unregister-input-001]
---

# wsm-near-json-boolean-mutation-output-001 exact Boolean mutation output

## Objective

Add the exact JSON Boolean return boundary needed by a later `storage_unregister` integration,
without changing raw scalar, explicit Unit, void, u128, or Promise terminals.

## Delivered

- Only the nominal one-leaf `JsonBooleanResult` schema binds `near-json-boolean-v1`; ordinary
  UInt64/Bool and same-shaped records do not bind it. The frame carries a checked `0/1`
  discriminant and is accepted only on mutating `Except Error (State × result)` entries.
- Successful `0` and `1` results persist all state fields before exactly one `value_return`, with
  exact unquoted bytes `false` and `true`. An out-of-range discriminant traps after staging state
  writes, and real nearcore proves transaction rollback.
- View, malformed-frame, and Promise-return combinations reject. Existing explicit Unit remains
  JSON `null`, while annotated void returns empty bytes; this capability changes neither.

## Boundary

This is a target-owned output prerequisite, not a generic JSON Boolean serializer or a public
NEP-145 method. The later operation owns exact-one-yocto, registration/supply/reclaim/refund
semantics and chooses the Boolean discriminant.
