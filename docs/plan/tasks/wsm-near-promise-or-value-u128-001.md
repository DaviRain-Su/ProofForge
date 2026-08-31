---
id: wsm-near-promise-or-value-u128-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-mutation-output-001, wsm-near-promise-002]
---

# wsm-near-promise-or-value-u128-001 dual NEAR terminal

## Objective

Allow one explicitly compiler-owned mutating U128 boundary to return either immediate quoted JSON
or one staged Promise without weakening ordinary UInt128, Unit, view, or Promise output rules.

## Delivered

- `pf_near_promise_or_value` binds only `Except Error (State × UInt128)` mutators to
  `near-promise-or-json-u128-v1`. The annotation is target-owned and digest-visible; duplicate,
  foreign, view, wrong-frame, and `pf_near_void` combinations reject.
- Each control-flow branch remains statically owned: no staged returned Promise emits exact quoted
  U128 through one `value_return`; exactly one staged returned Promise emits only `promise_return`.
  Ordinary mutating U128 retains `near-json-u128-string-v1` and still rejects Promise effects.
- Both terminals follow all state stores. Target checks pin asymmetric independent output limbs,
  two state fields, conditional helper/import inclusion, one terminal per branch, and no accidental
  generic Promise/value overloading.
- near-sandbox observes exact immediate quoted bytes and exact forwarded child bytes, with both
  independent state fields persisted before either result becomes observable.

## Boundary

This is the target terminal prerequisite for near-sdk's `PromiseOrValue<U128>` behavior. It does
not itself add receiver business logic, generated serde input, or a new standard export.
