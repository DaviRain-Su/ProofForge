---
id: wsm-near-storage-balance-bounds-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-output-001, wsm-near-storage-balance-output-001]
---

# wsm-near-storage-balance-bounds-output-001 bounded StorageBalanceBounds JSON output

## Objective

Add the exact output prerequisite for a later `storage_balance_bounds`-shaped view without choosing
global bounds for ProofForge's variable AccountId-length economics or exposing a standard method.

## Delivered

- Compiler-owned `StorageBalanceBoundsResult` has exactly five source leaves: minimum `(w0,w1)`,
  maximum presence, and maximum `(w0,w1)`. Only that nominal schema selects
  `near-json-storage-balance-bounds-v1`; ordinary same-shaped records do not.
- View-only target lowering emits exact declaration-order
  `{"min":"<u128>","max":null}` or `{"min":"<u128>","max":"<u128>"}`. Absent maximum
  requires zero inactive limbs; presence outside 0/1, malformed frame size, mutation, and Promise
  combination fail closed.
- The emitter reuses one decimal helper and 39-byte scratch span. The exact maximum bounded object
  arena is 97 bytes; a 39-digit minimum with unbounded maximum is exactly 60 bytes. Each runtime
  branch invokes `value_return` exactly once.
- Structural and real nearcore scenes pin zero, 2^64, 2^64+1, asymmetric limbs, max/max, null
  maximum, malformed presence/inactive data, write-free views, and repeated-call stale isolation.

## Boundary

The bytes match current near-sdk `StorageBalanceBounds`: quoted-decimal `min` and nullable quoted
`max`. The standards trait lets each contract choose global bounds, while the stock fungible-token
implementation reports one fixed measured cost as both min and max. ProofForge's current closed
registration policy instead has account-specific costs, so selecting its truthful global min/max
remains a separate policy slice. This output prerequisite exports no `storage_balance_bounds`,
accepts no JSON input, and claims no complete NEP-145 compatibility.
