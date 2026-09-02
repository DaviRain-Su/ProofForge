import ProofForge

/-!
One nested JSON leaf: slot `user_bal` → `{user:{bal}}` on AlphaNet
(`set_data_nested_object_field`). Not a Map. Digit-suffix slots like `xs_0`
stay flat. `credit` takes one UINT64 via `function_param`.
-/
namespace Examples.Xrpl.XrplNest
structure State where
  user_bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { user_bal := 0 }

/-- Add `delta` to nested `user.bal`. Zero-arg credit is gone; public ABI is live. -/
@[pf_entry]
def credit (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.user_bal ≤ u64Max - delta then
    .ok ({ user_bal := s.user_bal + delta }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.user_bal

end Examples.Xrpl.XrplNest