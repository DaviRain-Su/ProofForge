---
id: wsm-near-ft-transfer-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-transfer-input-001, wsm-near-void-output-001, wsm-near-fungible-ledger-001]
---

# wsm-near-ft-transfer-001 integrated fungible-token transfer

## Objective

Compose the existing bounded transfer arguments, closed `BAL2` ledger, exact NEP-141 event, and
omitted-return wrapper into the exact `ft_transfer` operation shape without overstating JSON ABI
compatibility.

## Delivered

- The exact snake-case payable export requires full-u128 attached deposit equal to one yoctoNEAR,
  predecessor different from receiver, positive amount, and present exact-16-byte registrations
  for both accounts. Missing or malformed values, insufficient funds, and destination overflow
  trap before either balance write.
- Checked two-limb source subtraction and receiver addition complete before source-then-receiver
  writes. A depleted source remains a present zero registration and integrated supply limbs never
  change. Nearcore transaction rollback covers synchronous failure after the first host write.
- Missing/null memo emits the exact no-memo v1.0.0 event; Some-empty and other bounded UTF-8 values
  emit the memo field with serde-compatible escaping. The event follows both balance effects and
  success performs no `value_return`, yielding exact empty SuccessValue bytes.
- Targeted extraction/IR/WAT checks pin two reads before two writes, payable input/output policies,
  exact export, event ordering, and absent remove/value-return calls. Near-sandbox covers guard,
  registration, malformed values, arithmetic, rollback, high limbs, present zero, optional memo
  bytes, one exact log, conservation, and empty output.

## Compatibility boundary

Operation, event, and successful return behavior match the pinned near-contract-standards path,
but arguments use `near-json-ft-transfer-args-bounded-v1`: 786 wire bytes, 32 structural whitespace
bytes, raw known keys, unknown-field rejection, AccountId bounds, and a 16-byte decoded memo.
Those restrictions are narrower than generated serde_json wrappers, so this is not a claim of
complete public NEP-141 ABI compliance. Registration management, resolver callbacks, and storage
deposit policy remain separate.
