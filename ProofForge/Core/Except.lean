import ProofForge.Attr

namespace ProofForge.Core.Except

/-!
# Target-neutral `Except` helpers

Small combinators for contract entry bodies. Extraction lowers `bind` to the same join shape
already used by hand-written `match` on `Except`; there is no new Runtime leaf or emitter case.
-/

/-- Lift a value into a successful result. -/
@[pf_inline] def ok (value : α) : Except ε α := .ok value

/-- Fail with the caller's explicit error value. -/
@[pf_inline] def err (error : ε) : Except ε α := .error error

/-- Sequence one successful step into the next. Errors short-circuit without running `next`. -/
@[pf_inline] def andThen (step : Except ε α) (next : α → Except ε β) : Except ε β :=
  match step with
  | .ok value => next value
  | .error e => .error e

/-- Map a successful value; errors pass through unchanged. -/
@[pf_inline] def map (step : Except ε α) (f : α → β) : Except ε β :=
  match step with
  | .ok value => .ok (f value)
  | .error e => .error e

/-- Run `step` when the predicate holds; otherwise return `error`. -/
@[pf_inline] def guard (cond : Bool) (error : ε) (step : Unit → Except ε α) : Except ε α :=
  if cond then step () else .error error

end ProofForge.Core.Except
