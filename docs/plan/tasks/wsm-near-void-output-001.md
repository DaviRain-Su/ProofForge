---
id: wsm-near-void-output-001
scope: wasm
status: done
depends-on: [wsm-near-json-unit-output-001]
---

# wsm-near-void-output-001 omitted mutating return

## Objective

Match near-sdk's omitted-return mutating wrapper: persist successful state while returning exact
empty bytes, without changing explicit Unit JSON null or any historical output policy.

## Delivered

- Compiler-owned `pf_near_void` is accepted only on an exact zero-leaf Unit mutation. A view or a
  scalar/public result rejects. Other targets continue to reject the foreign target annotation.
- `near-void-empty-v1` participates in canonical target IR and emits no output allocation and zero
  `value_return` calls. Promise-return combination rejects; initializer, raw UInt64, quoted u128,
  and explicit Unit JSON-null behavior remain unchanged.
- Targeted extraction/IR/WAT checks pin schema, policy, digest, state writes and absent output host
  calls. The near-sandbox fixture proves exact empty SuccessValue, state persistence, repeated
  calls, failed-call rollback, and unchanged exact JSON null for explicit Unit.

## Authoritative boundary

Current near-contract-standards declares `ft_transfer` without an explicit Rust return type.
near-sdk macros classify that as `ReturnKind::Default`, serialize no result, and never call
`env::value_return`. This differs from explicit `-> ()`, whose default JSON serialization is
`null`; ProofForge keeps the two source policies separate.

## Next

Compose exact empty output with bounded transfer args, one-yocto validation, the `BAL2` ledger,
and the NEP-141 transfer event. The bounded input subset remains narrower than serde_json.
