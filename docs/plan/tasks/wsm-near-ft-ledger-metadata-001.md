---
id: wsm-near-ft-ledger-metadata-001
scope: wasm
status: done
depends-on: [wsm-near-ft-metadata-001, wsm-near-ft-transfer-call-001]
---

# wsm-near-ft-ledger-metadata-001 integrated metadata view

## Objective

Put the already verified bounded `ft_metadata` boundary on the same real artifact as the canonical
`BAL2` fungible ledger, without changing ledger, resolver, event, or Promise behavior.

## Delivered

- `NearFungibleLedger` exports exact `ft_metadata` beside `ft_total_supply`, `ft_balance_of`,
  `ft_transfer`, `ft_transfer_call`, and private `ft_resolve_transfer`.
- The method uses the same no-args request-ignore input and exact nominal 70-leaf output policy. Its
  fixed metadata matches the standalone configured value, including absent reference/hash fields.
- Structural tests pin no storage operations, exact export/policies, one 2929-byte arena, one
  `value_return`, and no writes/removes/logs/Promise. The real ledger sandbox calls empty, valid
  unknown-field, malformed, and repeated request bodies and proves exact bytes plus unchanged
  balances/supply/state before continuing all existing ledger and transfer-call scenes.

## Compatibility boundary

This is artifact composition, not a wider codec. ProofForge's 64/16/256/128 UTF-8 capacities remain
non-authoritative product limits; serialization does not automatically run `assert_valid`, and no
complete NEP-148 ABI claim is made.
