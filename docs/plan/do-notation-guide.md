# `do` notation with `Core.Except`

ProofForge contracts can use the shared `ProofForge.Core.Except` monad for
fail-fast control flow that extracts to target-specific error handling.

## Primitives

```lean
import ProofForge

open ProofForge.Core.Except

def step (n : UInt64) : Except MyError UInt64 :=
  guard (n < 100) .overflow >>= fun _ =>
  ok (n + 1)
```

- `ok x` — success
- `err e` — failure with a user-defined error type
- `guard cond err` — fail when `cond` is false
- `andThen` / `>>=` — sequence; failure short-circuits
- `map` — map the success value

Extract recognizes `Core.Except.andThen` like `Bind.bind` on the standard
`Except` type, so `do` notation desugars correctly for NEAR, EVM, and SVM.

## Example (NEAR)

See `Examples.NearTokenErgonomics` — `addCheckedViaAndThen` chains u128
overflow checks before returning an updated `NearToken`.

## Example (EVM / SVM)

- `Examples.EvmExceptErgonomics.addViaAndThen`
- `Examples.SvmExceptErgonomics.addViaAndThen`

## When to prefer `Except` over `if`

Use `Except` when multiple early exits share one error type and you want
linear readable flow without nested `if`/`else`. Keep pure arithmetic on
plain `UInt64` when no failure path exists — Extract stays simpler.

## Related

- Task: `docs/plan/tasks/erg-do-001.md`
- Next surface: `docs/plan/tasks/erg-evm-effect-001.md` (Token sequential `Effect`) —
  first slice landed as `Examples.EvmTokenErgonomics` (`Effect.ensure` / `abort`);
  `Examples.Evm.Token.approve` / `transfer` / `transferFrom` use Bool `Effect.ensure`;
  `mint` / `burn` use UInt64 `Effect.ensureCode` (digest pending pin after extract)
- NEAR PromiseHandle Extract through `and8Returned` landed (N13); see `wsm-near-promise-general-001`
