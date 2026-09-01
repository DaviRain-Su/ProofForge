import ProofForge

/-!
Independent consumer of target-neutral parameterized source errors. Error constructors stay
ordinary Lean data: Core preserves their named fixed fields, while EVM derives the selector,
argument words, and ABI declaration from that one descriptor.
-/

namespace Examples.EvmTypedErrors

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | denied (code : UInt64)
  | conflict (expected : UInt64) (actual : UInt64)
  | exhausted (current : UInt64) (requested : UInt64) (authorization : UInt64) (limit : UInt64)
  | locked
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def valueOf (s : State) : UInt64 :=
  s.value

/-- Authorization, conflict, and application lock checks all precede the only state update. -/
@[pf_entry]
def update (s : State) (next authorization : UInt64) : Except Error (State × UInt64) :=
  if authorization == 8 then
    .error (.exhausted s.value next authorization 7)
  else if authorization != 7 then
    .error (.denied authorization)
  else if next == s.value then
    .error (.conflict s.value next)
  else if next == 0 then
    .error .locked
  else
    .ok ({ value := next }, next)

end Examples.EvmTypedErrors
