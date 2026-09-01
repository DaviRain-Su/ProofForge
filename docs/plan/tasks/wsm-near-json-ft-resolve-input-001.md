---
id: wsm-near-json-ft-resolve-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-transfer-input-001, wsm-near-promise-json-u128-result-001]
---

# wsm-near-json-ft-resolve-input-001 bounded private resolver arguments

## Objective

Decode the exact callback argument object `{sender_id,receiver_id,amount}` into two complete
AccountIds and one lossless u128 without adding Promise-result or ledger reconciliation behavior.

## Delivered

- Compiler-owned `FtResolveTransferArgs` has exactly sender AccountId9, receiver AccountId9, and
  amount2 leaves. Ordinary same-shaped records, missing leaves, and extra leaves do not select its
  target policy. Both view and mutating wrappers can reuse it.
- `near-json-ft-resolve-args-bounded-v1(max-wire=1079,ws=32,order=any,keys=raw,unknown=reject)`
  accepts all six known-field permutations. Each required field has an independent presence bit;
  duplicates, missing/unknown/escaped keys, wrong types, trailing input, and malformed values trap.
- The maximum derives from 45 structural bytes, two 64-byte AccountIds and 39 decimal digits each
  in worst-case six-byte escapes, plus 32 aggregate whitespace bytes. Account syntax remains exact
  2..64 canonical ASCII, amount parsing remains full checked u128, and both pre-zeroed AccountId
  frames expose only active bytes.
- Targeted IR/WAT checks pin schema, 20 locals, policy/digest, one bounded field loop, a 160-byte
  zeroed frame, and no standard export or Promise-result import. near-sandbox covers six orders,
  equal/distinct and raw/escaped identities, mixed/max amounts, exact/above bounds, malformed and
  late-failure matrices, inactive-zero isolation, mutating use, and failed-call rollback. The old
  combined transfer parser remains a separate regression gate.

## Boundary

This is a bounded canonical subset rather than serde_json compatibility: keys must use raw exact
spelling, unknown fields reject, and structural whitespace is capped. It does not implement or
export `ft_resolve_transfer`, inspect a Promise result, enforce private/self callback policy, or
touch the BAL2 ledger. Those compose only in the subsequent resolver slice.
