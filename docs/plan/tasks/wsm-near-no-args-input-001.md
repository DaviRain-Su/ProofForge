---
id: wsm-near-no-args-input-001
scope: wasm
status: done
depends-on: [wsm-near-ft-total-supply-001, wsm-near-storage-balance-bounds-001]
---

# wsm-near-no-args-input-001 explicit near-sdk no-args wrapper

## Objective

Match current near-sdk generated methods with no regular arguments without globally weakening
ProofForge's historical exact-empty zero-parameter boundary.

## Delivered

- Compiler-owned `@[pf_near_no_args]` binds only an exact zero-parameter non-initializer to
  canonical target policy `near-no-args-ignore-input-v1`. The policy and logical Unit input schema
  participate in the program digest.
- The generated wrapper performs no `input`, `register_len`, or `read_register` call. Empty bytes,
  `{}`, malformed/non-UTF8 bytes, and large request bodies therefore reach the same method body,
  matching current near-sdk's generated no-args wrapper.
- `ft_total_supply` and `storage_balance_bounds` opt in explicitly. Other zero-parameter methods
  retain the prior exact-empty guard. Duplicate annotations, initializers, and parameterized methods
  fail target binding.
- Structural and real nearcore tests pin both opted-in standard views, unchanged output/state, and
  the retained legacy guard on an unannotated method.

## Compatibility boundary

This policy only matches the no-regular-arguments wrapper boundary. It does not add generic JSON,
change the bounded argument subsets of other public-shaped methods, or turn the variable storage
economics into stock fixed-cost NEP-145 policy.
