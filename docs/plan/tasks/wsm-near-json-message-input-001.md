---
id: wsm-near-json-message-input-001
scope: wasm
status: done
depends-on: [wsm-near-json-memo-input-001]
---

# wsm-near-json-message-input-001 required bounded message JSON input

## Objective

Add the required bounded UTF-8 `msg` parser prerequisite for a later specialized
`ft_transfer_call` argument object without adding Promise behavior or a standard export.

## Delivered

- Compiler-owned `BoundedMessage64` is exactly `(length,w0..w7)`. Decoded active bytes are packed
  little-endian and all inactive bytes/words are zero; ordinary bounded strings and ordinary
  same-shaped records do not select this target policy. View and mutating wrappers both reuse it.
- The canonical one-field object requires a raw-spelled `msg` key and string value. Empty message
  is valid; missing, null, wrong type, unknown/duplicate key, escaped key, and trailing input reject.
  Aggregate structural SP/TAB/LF/CR is independently limited to 32 bytes.
- The parser parameterizes and reuses the optional-memo string cursor. Raw valid UTF-8, JSON short
  escapes, BMP escapes, and valid surrogate pairs decode identically; malformed UTF-8, controls,
  bad escapes/hex, and isolated/reversed surrogates fail closed.
- Decoded capacity is 0..64 UTF-8 bytes. The exact 426-byte wire bound is ten object bytes, sixty-four
  worst-case six-byte escapes, and 32 structural whitespace bytes. Targeted WAT pins the loop-based
  shared decoder and exact 72-byte frame; near-sandbox pins packed limbs, inactive zero, mutation,
  exact bounds, Unicode, and malformed matrices.

## Boundary

This is a deliberately bounded canonical subset, not serde_json compatibility. It is a diagnostic
input codec only: it does not expose `ft_transfer_call`, compose receiver payloads, or create a
Promise. The next prerequisite owns dynamic receiver function-call staging and payload composition.
