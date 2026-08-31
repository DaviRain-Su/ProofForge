# wsm-near-promise-account-transfer-001 — NEAR full-AccountId native Promise transfer

Status: done

Depends on: [wsm-020](wsm-020.md),
[wsm-near-u128-001](wsm-near-u128-001.md),
[wsm-near-memory-001](wsm-near-memory-001.md),
[wsm-near-promise-transfer-001](wsm-near-promise-transfer-001.md)

## Scope

Add closed `Near.Sdk.Promises.transferAccountDetached` and
`transferAccountReturned` APIs alongside the byte-compatible static receiver APIs:

- accept the complete nine-leaf nominal `Runtime.AccountId` and a lossless two-limb `NearToken`;
- require receiver length 2..64 and stage exactly that many active raw AccountId bytes directly
  from the carrier, without a Borsh length, JSON escaping, truncation, or inactive padding;
- reuse the exact aligned 16-byte little-endian amount frame and host sequence
  `promise_batch_create` then `promise_batch_action_transfer`;
- keep detached lifecycle independent of the method result; the returned form persists caller
  state before exactly one `promise_return` of the created Promise index;
- reject the effect from views, reject statically known length 1/65 receivers during extraction,
  and retain runtime length guards for context-sourced geometry.

Context host calls supply syntactically valid nominal AccountIds. This layer checks geometry only;
manually constructed future values require validation before they reach this API. Promise creation
does not mean the child receipt will succeed, and returned propagation does not make the transfer
synchronous. This slice does not add registration/refund policy, public JSON ABI, generic Promise
handles, or multi-action builders.

## Verification

- `Tests.NearPromiseSpec` pins Runtime→Extract→target IR effect counts, canonical caller/self and
  literal 2/64-byte frames, active-byte stores through byte 63, inactive-padding exclusion, exact u128
  high/low staging, create/action/state/return order, and rejection of length 1/65 fixtures.
- `runtime-tests/near/check.sh` anchors the registered dynamic exports and staging geometry.
- `runtime-tests/near/promise.sh` deploys on near-sandbox 2.13.0, transfers to a distinct existing
  receiver from a padded carrier with an exact 19-yocto balance delta, creates a zero-amount self
  receipt, and returns a transfer to the complete dynamic predecessor. The static transfer scenes
  remain byte-exact regressions.

## Next

Closed storage registration economics may now compose measured usage, trusted per-byte cost,
checked u128×u64, attached deposit, and this dynamic refund edge. It must remain separate from
public NEP-145 method ABI and define duplicate/unregister/balance policy explicitly.
