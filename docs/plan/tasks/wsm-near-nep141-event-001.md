---
id: wsm-near-nep141-event-001
scope: wasm
status: done
depends-on: [wsm-near-event-001, wsm-020, wsm-near-u128-001]
---

# wsm-near-nep141-event-001 exact no-memo ft_mint event

## Objective

Add the first standard-specific NEP-141 event serializer after the bounded NEP-297 substrate,
without claiming fungible-token state, methods, storage, or a generic JSON ABI.

## Delivered

- `Sdk.Events.FungibleToken.mint(owner, amount)` lowers through the irreducible
  `Runtime.nep141FtMint` effect and complete Extract/Ops/IR/CFG/canonical payload.
- The emitter reconstructs all active bytes of the complete 64-byte AccountId frame and applies
  JSON escaping before writing the exact compact NEP-141 v1.0.0 envelope. `data` is one record,
  field order is `owner_id`, then `amount`; amount is quoted decimal and `memo` is omitted.
- Full u128 decimal conversion keeps 39 little-endian digits. Source bits are consumed 127 down to
  0, each bit enters carry at digit 0, digits update 0 through 38, and output scans 38 down to 0.
  Zero emits exactly `0`.
- Serialization uses the checked invocation-local arena and performs exactly one final
  `env.log_utf8` call.

## Verification

- Lean guards pin the complete nine-leaf owner plus two-limb amount effect, canonical digest,
  decimal loop invariants, 528-byte envelope worst case, 39-byte decimal scratch, no memo, and all
  four fixture exports.
- near-sandbox compares exact logs for amounts 0, 2^64, 2^64 + 1, and 2^128 - 1, including the
  full predecessor AccountId and one committed state transition per event.

## Not included

- `ft_transfer`, `ft_burn`, balances, total supply, storage management, resolver callbacks, memo
  support, arbitrary event record arrays, or a complete NEP-141 fungible-token contract.
