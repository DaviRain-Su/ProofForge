---
id: wsm-near-u128-arithmetic-001
scope: wasm
status: done
depends-on: [wsm-near-u128-001]
---

# wsm-near-u128-arithmetic-001 checked NearToken arithmetic

## Objective

Provide the lossless two-limb arithmetic prerequisite for a later internal NEP-141 ledger without
adding storage layout, public FT methods, or JSON ABI.

## Delivered

- Six pure target-owned values take `left.w0,left.w1,right.w0,right.w1`: checked add/sub
  predicates and the corresponding modular low/high result limbs.
- Addition propagates the unsigned low-limb carry and rejects either high-limb overflow;
  subtraction propagates borrow and accepts exactly `left ≥ right` under unsigned lexicographic
  comparison.
- `Sdk.NearToken.canAdd/canSub` own the preconditions. `addW0/addW1/subW0/subW1` are explicitly
  documented as result limbs usable only after the matching predicate, following the existing
  closed SDK policy style.
- Runtime, Extract, target Ops/IR/CFG canonicalization, and WAT emission preserve little-endian
  limb order. Wasm comparisons are unsigned and comparison bits use `i64.extend_i32_u`.

## Verification

- Targeted extraction pins all six arity-four values, canonical spellings, digest, and WAT
  unsigned/carry/borrow instructions.
- near-sandbox checks zero-crossing carry, max-u128 overflow, high-bit unsigned addition,
  2^64 borrow, underflow, high-bit unsigned subtraction, and view purity.

## Not included

- Borsh u128 storage codec, full AccountId map keys, balances, total supply, registration,
  storage management, FT events sequencing, public methods, or complete NEP-141 compliance.
