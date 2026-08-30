---
id: wsm-near-nep141-event-002
scope: wasm
status: done
depends-on: [wsm-near-nep141-event-001]
---

# wsm-near-nep141-event-002 exact no-memo transfer and burn events

## Objective

Complete the official NEP-141 v1.0.0 event variants over the existing closed fungible-token event
serializer, without adding fungible-token state, methods, storage, or a generic JSON ABI.

## Delivered

- `Sdk.Events.FungibleToken.transfer(oldOwner, newOwner, amount)` and `burn(owner, amount)` lower
  through irreducible Runtime effects and complete Extract/Ops/IR/CFG/canonical payloads.
- Transfer emits one data record in official order `old_owner_id`, `new_owner_id`, `amount`; burn
  emits `owner_id`, `amount`. Amount is a quoted full-u128 decimal and `memo` is omitted.
- Both complete AccountId frames pass through the existing bounded JSON escaper. The shared closed
  event staging reuses the checked arena and 39-digit decimal routine, then performs exactly one
  final `env.log_utf8` call.

## Verification

- Lean guards pin two nine-leaf transfer owners, one nine-leaf burn owner, limb order, canonical
  digest, 938/528-byte worst-case envelopes, no memo, and fixture exports.
- near-sandbox compares exact compact logs for a transfer between distinct complete accounts at
  max-u128 and a burn at 2^64, including exact field order and one committed transition per event.

## Not included

- Balances, total supply, FT method ABI, storage management, resolver callbacks, memo support,
  arbitrary event arrays, or a complete NEP-141 fungible-token contract.
