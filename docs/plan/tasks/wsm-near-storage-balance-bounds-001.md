---
id: wsm-near-storage-balance-bounds-001
scope: wasm
status: done
depends-on: [wsm-near-storage-balance-bounds-output-001, wsm-near-storage-balance-of-001]
---

# wsm-near-storage-balance-bounds-001 variable registration bounds view

## Objective

Expose truthful global bounds for the closed variable AccountId-length registration policy through
an exact `storage_balance_bounds`-shaped view, without changing registration or claiming complete
NEP-145 ABI compatibility.

## Delivered

- Exact `storage_balance_bounds` returns quoted full-u128 minimum and maximum costs using the same
  trusted per-byte price as registration. The compiler-owned AccountId syntax is authoritative
  nearcore/near-account-id 2..64 bytes, so the exact entry geometries are `2 + 64 = 66` and
  `64 + 64 = 128` bytes.
- Both multiplications are checked before output. Zero trusted price or either overflow selects an
  invalid output discriminator and traps; no plausible but false bound is returned.
- The view performs no map read, storage write/remove, log, or Promise effect. Structural checks pin
  zero parameters, the exact output policy, snake-case export, empty-input guard, geometry, and
  source-effect freedom.
- Real nearcore scenes verify exact min/max bytes before and after registration lifecycle changes,
  high-limb decimal output, `{}`/arbitrary nonempty input rejection, overflow/zero-price failure,
  and write-free success/failure.

## Boundary

Current near-account-id 2.0.0 and ProofForge's static, single-field, and shared multi-field parsers
all reject one-byte IDs; registration uses host `Context.caller`, which nearcore already validated.
The 66-byte minimum is therefore consistent with the complete accepted registration/query set.
Nearcore account-creation policy may restrict who can create short top-level IDs, but does not
change AccountId syntax or this contract's global accepted geometry.

The stock near-contract-standards FT reports one fixed max-account measurement as both bounds;
ProofForge intentionally reports the extrema of its variable policy. The later
`wsm-near-no-args-input-001` slice opts this exact method into near-sdk's generated no-argument
request-ignore behavior without changing other zero-parameter methods. This slice does not add storage deposit/withdraw,
arbitrary-account mutation, automatic ledger enforcement, or full NEP-145 compatibility.
