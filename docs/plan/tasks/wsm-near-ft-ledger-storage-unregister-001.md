# wsm-near-ft-ledger-storage-unregister-001

Status: done

## Goal

Compose public-shaped `storage_unregister` into the same integrated `NearFungibleLedger` BAL2
registration/balance namespace without introducing another map or changing FT transfer policy.

## Contract

- exact one attached yocto; predecessor is always target and refund recipient;
- missing registration logs `The account <id> is not registered`, returns JSON `false`, and does
  not mutate storage/supply or create a refund;
- present zero removes the BAL2 key, preserves supply, refunds variable retained cost plus one;
- positive balance rejects unless `force:true`; forced removal prechecks and subtracts exact supply,
  removes the key, refunds cost plus one, and emits no FT event;
- bounded optional-force input and exact JSON Boolean output are reused unchanged.

## Boundary

The integrated fixture uses immutable 1 yocto/byte pricing and checked u128 refund addition. Its
47-byte bounded canonical JSON subset rejects unknown/escaped keys and excess whitespace. These
are explicit differences from full near-sdk/near-contract-standards compatibility; detached refund
failure also cannot roll back an already successful parent receipt.

## Evidence

`Tests.NearFungibleLedgerSpec` pins exact schema/policies, canonical digest, BAL2 read/remove shape,
and remove-before-refund ordering. The real nearcore ledger suite covers missing/log/false,
present-zero, non-force rollback, forced-positive supply burn, exact `S + 1` refunds, and no event.
