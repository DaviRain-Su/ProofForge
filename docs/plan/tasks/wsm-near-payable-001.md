# wsm-near-payable-001 — NEAR non-payable entry guards

Status: done

Depends on: [wsm-near-init-001](wsm-near-init-001.md),
[wsm-near-u128-001](wsm-near-u128-001.md)

## Scope

Apply NEAR's non-payable-by-default wrapper policy to initializers and mutating entries:

- before input decoding, read the full 16-byte little-endian attached deposit and reject either
  nonzero word with the exact `Method <name> doesn't accept deposit` panic;
- emit no deposit guard for views;
- treat explicit use of `Context.attachedDeposit` (including either full-width word projection) as
  the current source-level payable capability and retain its lossless u128 read;
- keep method-specific panic bytes in a bounded target-owned static region included in arena and
  initial-memory accounting.

This capability rule is deliberately narrower than near-sdk-rs `#[payable]`: a method cannot yet
accept a donation without observing the deposit. General target entry metadata remains future work.
Inlining and extraction materialize Runtime deposit leaves into the consuming method before this
policy is classified.

## Verification

- `Tests.NearSpec` pins the import, guard-before-input order, both u128 words, method-specific panic,
  initializer ordering, and absence of a guard from views.
- Existing `Tests.NearCtxSpec` and sandbox context scenes retain >u64 deposits for the three methods
  that explicitly observe attached deposit.
- `runtime-tests/near/counter.sh` verifies exact paid-initializer and paid-mutator rejection, then
  proves initialization can still succeed and state remains unchanged after the rejected mutator.

## Next

Add reusable private entry metadata rather than inferring callback privacy from body logic. Donation-
only payable methods should arrive with that same target-owned entry-policy channel.
