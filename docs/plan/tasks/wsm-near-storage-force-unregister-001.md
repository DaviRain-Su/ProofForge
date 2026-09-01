---
id: wsm-near-storage-force-unregister-001
scope: wasm
status: done
depends-on: [wsm-near-storage-unregister-001, wsm-near-fungible-ledger-001]
---

# wsm-near-storage-force-unregister-001 supply-integrated forced removal

## Objective

Integrate caller-only unregister with the existing exact balance map and lossless total supply,
without adding public NEP-145 JSON methods, arbitrary-account policy, or a second balance store.

## Authoritative behavior

Current near-sdk-rs `internal_storage_unregister(force)` runs `assert_one_yocto`, reads the
predecessor balance, rejects positive balance unless force is true, removes the account, directly
subtracts that balance from `total_supply`, and detaches the fixed-minimum-plus-one refund. Missing
logs and returns `None`. It does **not** call an internal burn helper or emit NEP-141 `ft_burn`;
the transfer-resolution deleted-sender path is separate and does emit a burn with memo `refund`.

## Delivered

- `forceUnregisterCaller(force : UInt64)` accepts only closed Boolean 0/1 and exact attached one
  yocto before host writes. It reads the same `BAL2` map used by registration and the ledger.
- Present values require status/fits/exact16; both limbs are snapshotted before another host call.
  Positive balance with force=0 and malformed values fail before remove. Full-u128 supply
  subtraction is checked before remove; zero balance follows the same path without changing supply.
- Only after all balance/supply checks does it sample usage, remove, sample reclaim, check
  full-u128 `reclaim × trustedPrice` and `+1`, then stage the exact dynamic caller refund. The
  returned state persists the precomputed reduced supply last.
- Sandbox scenes pin mixed-limb and max-u128 burns, zero-force behavior, force=false rejection,
  supply underflow, malformed value, exact successful transfer receipts, conservation, and
  multiplication/addition overflow rollback after speculative removal.

## Atomicity and event boundary

Synchronous post-remove failures panic and rely on nearcore executing-receipt atomic rollback for
map, supply state, balance, and staged receipts. A later detached refund receipt failure cannot
restore committed removal. Following current near-contract-standards, forced removal emits no
`ft_burn`; therefore this remains a closed internal policy, not complete NEP-141/145 compliance.

## Not included

Public JSON ABI, arbitrary account, storage withdrawal, resolver, automatic registration checks in
token methods, forced-burn event policy beyond near-sdk behavior, or synchronous refund delivery.
