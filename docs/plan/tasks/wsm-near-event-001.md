---
id: wsm-near-event-001
scope: wasm
status: done
depends-on: [wsm-near-log-dynamic-001, wsm-near-memory-001]
---

# wsm-near-event-001 bounded NEP-297 string events

## Objective

Add one closed, bounded NEP-297 string-data serializer over `env.log_utf8` without claiming a
generic JSON ABI or a complete standard contract.

## Delivered

- `Sdk.Events.writeStringData` lowers through the irreducible `Runtime.nep297StringData` effect and
  typed Extract/Ops/IR/CFG payloads. Standard, version, and event are compile-time strings; data is
  one `BoundedString capacity` frame.
- The target emits exactly
  `EVENT_JSON:{"standard":"...","version":"...","event":"...","data":"..."}` in one host log.
  Metadata and dynamic bytes follow serde_json-compatible escaping: quote/backslash and short
  controls use short escapes, remaining C0 controls use lowercase `\u00xx`, slash and DEL pass
  through, and validated UTF-8 bytes are preserved.
- The checked arena allocation is the exact static-prefix + `6 * capacity` + static-suffix worst
  case. Active leaves are byte-checked and one final `env.log_utf8` owns the observable effect.
- NEAR limits remain host-owned: at most 100 logs and 16,384 cumulative log bytes per receipt.
  This slice emits one bounded log and does not introduce receipt-wide budget state.

## Verification

- NearBytes guards pin the exact effect frame, canonical digest, worst-case allocation, JSON escape
  branches, host import, and final call.
- near-sandbox scenes compare exact compact envelopes for empty/ASCII, quote, backslash, slash,
  short and `\u00xx` controls, DEL, multibyte UTF-8, and escaped compile-time metadata.

## Not included

- Generic JSON method ABI, arrays/objects selected by source code, NEP-141 state or methods, or a
  full fungible-token contract.
