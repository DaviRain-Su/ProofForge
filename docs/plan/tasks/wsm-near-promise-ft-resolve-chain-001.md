---
id: wsm-near-promise-ft-resolve-chain-001
scope: wasm
status: done
depends-on: [wsm-near-promise-ft-on-transfer-001, wsm-near-ft-resolve-transfer-001]
---

# wsm-near-promise-ft-resolve-chain-001 weighted child/resolver chain

## Objective

Compose the existing specialized weighted `ft_on_transfer` call with the private fungible-token
resolver callback without adding a generic Promise API or prematurely exporting `ft_transfer_call`.

## Delivered

- `ftOnTransferThenResolveReturned` fixes the complete DAG: dynamic receiver batch, weighted
  `ft_on_transfer` action with zero deposit/gas and weight one, dependent callback batch on the full
  current AccountId, then weighted `ft_resolve_transfer` with zero deposit, 5 Tgas, and weight zero.
  Only the callback promise is returned after caller-state persistence.
- The child and callback JSON payloads use independent checked arenas. The child retains its exact
  sender/amount/message serializer. The callback composes exact
  `{"sender_id":"...","receiver_id":"...","amount":"..."}` bytes; its 852-byte allocation is
  45 structural bytes + two 64-byte frames at six-byte worst-case escaping + 39 decimal digits.
- The API exposes no receiver method, callback method, deposit, gas, or weight controls. It performs
  no initial BAL2 transfer and exports no standard fungible-token method.

## Verification

Targeted extraction/WAT checks pin frame geometry, both method literals, separate 844/852 arenas,
two zero-u128 deposits, create → child action → then → callback action ordering, exact gas/weights,
and state writes before `promise_return(callback)`. Near-sandbox deploys partial, over-amount,
malformed, and failing children and drives the real private resolver over BAL2, covering registered
sender refunds, deleted-sender burn, present-zero retention, exact events/supply, and quoted outer
results. Existing static and dynamic Promise scenes remain green.

## Next

The next independent slice may compose bounded `ft_transfer_call` input, exact one-yocto and initial
ledger transfer/event with this chain. This prerequisite alone is not a public NEP-141 method.
