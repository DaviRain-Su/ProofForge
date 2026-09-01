---
id: wsm-near-log-dynamic-001
scope: wasm
status: done
depends-on: [wsm-near-log-001, wsm-near-bytes-001, wsm-near-memory-001]
---

# wsm-near-log-dynamic-001 NEAR bounded dynamic UTF-8 logging

## Objective

Extend the existing static `env.log_utf8` effect to a source `BoundedString capacity` without
introducing target pointers or an unbounded allocator API.

## Delivered

- `Sdk.Logs.writeBounded` lowers through an irreducible Runtime effect to a typed
  `logUtf8Bounded(capacity, length + bytes)` payload. Capacities use the existing NEAR 1..64 byte
  bound and all payload values participate in CFG mapping, validation, and canonical digests.
- The emitter reuses the checked invocation-local arena frame: it traps when length exceeds
  capacity or an active leaf exceeds one byte, stores only the active prefix, then calls the
  official `log_utf8(length, pointer)` ABI. Dynamic-only contracts still import the host function.
- Canonical NEAR `BoundedString` input validates strict UTF-8 before source execution. Internally
  constructed values retain the source `BoundedString.wellFormed` obligation.
- Logging remains legal in views and preserves source sequencing. The NearBytes fixture proves
  the continuation by returning the logged byte length.

## Verification

- Compile-time guards pin the exact nine-value effect frame, arena allocation, host import/call,
  active-byte checks, and canonical digest.
- near-sandbox scenes observe exact empty, partial, full-capacity, ASCII, and multibyte logs and
  reject malformed UTF-8 before the dynamic log effect executes.

## Not included

- NEP-297 `EVENT_JSON:` serialization, JSON escaping, internally constructed-string validation,
  or receipt-wide log budget accounting.
