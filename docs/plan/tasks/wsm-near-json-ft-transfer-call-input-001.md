---
id: wsm-near-json-ft-transfer-call-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-transfer-input-001, wsm-near-json-message-input-001]
---

# wsm-near-json-ft-transfer-call-input-001 bounded transfer-call arguments

## Objective

Decode the four-field fungible transfer-call argument shape into one exact compiler-owned frame
without exporting `ft_transfer_call` or coupling parsing to ledger and Promise behavior.

## Delivered

- `FtTransferCallArgs` is exactly 24 scalar leaves: AccountId9, u128 amount2, OptionalMemo16 four,
  and BoundedMessage64 nine. Ordinary records and incomplete lookalikes do not bind.
- `near-json-ft-transfer-call-args-bounded-v1` accepts required raw keys `receiver_id`, `amount`,
  and `msg`, optional `memo` (missing/null=None; empty string=Some empty), in any order. Duplicate,
  unknown, escaped, missing, wrong-type, trailing, and malformed values fail closed.
- One field loop reuses the established AccountId, checked quoted-u128, and Unicode string value
  decoders. Receiver, memo, and message have independent active geometry; all inactive bytes are
  zero. The exact wire maximum is 1179 bytes: 49 structural + worst-case escaped 64/39/16/64-byte
  values + 32 aggregate whitespace bytes.

## Boundary

This remains a bounded canonical subset, not near-sdk serde compatibility: raw known keys only,
unknown fields rejected, and aggregate whitespace/wire limits apply. The diagnostic fixture has no
token write, Promise effect, or standard export. The next slice composes this parser with the
integrated BAL2 transfer, event, and specialized resolver chain.
