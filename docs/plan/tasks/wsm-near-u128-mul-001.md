---
id: wsm-near-u128-mul-001
scope: wasm
status: done
depends-on: [wsm-near-u128-arithmetic-001, wsm-near-storage-economics-001]
---

# wsm-near-u128-mul-001 checked NearToken by UInt64 multiplication

## Objective

Add the exact arithmetic prerequisite for `storage bytes × trusted NearToken per-byte cost`, without
choosing a protocol price or implementing registration.

## Delivered

- `NearToken.canMulUInt64`, `mulUInt64W0`, and `mulUInt64W1` preserve a full u128 value and an
  unsigned u64 factor through Runtime, extraction, target Ops/IR, and canonical emission.
- Two shared WAT helpers synthesize exact u64×u64 low/high limbs from unsigned 32-bit halves. For
  `(hi·2^64 + lo)·factor`, validity requires both the high half of `hi·factor` to be zero and the
  cross-product high-limb addition not to overflow. Result limbs are consumed only after validity.
- The helpers are emitted once and only when multiplication leaves are reachable; this avoids a
  large per-call unrolled expansion.

## Verification

Targeted extraction pins arity-three operand order, canonical spellings, helper calls, and digest.
near-sandbox covers token/factor zero, mixed limbs, max-u64 square, max-u128 × 1/2, exact maximum,
high-limb exact fit, cross-product carry overflow with `hiHi = 0`, and the maximum successful high
result limb. Every method is a view and leaves storage unchanged.

## Not included

Generic u128×u128 multiplication, a storage-byte price constant, registration/refund policy,
dynamic-account Promise transfer, public JSON ABI, or NEP-145 compliance.
