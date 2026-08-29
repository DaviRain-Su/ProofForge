import ProofForge

/-!
One nested JSON leaf: slot `user_bal` → `{user:{bal}}` on AlphaNet
(`set_data_nested_object_field`). Not a Map. Digit-suffix slots like `xs_0`
stay flat. Zero-arg for public RPC.
-/
namespace Examples.XrplNest

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

@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if s.user_bal ≤ u64Max - 1 then
    .ok ({ user_bal := s.user_bal + 1 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.user_bal

end Examples.XrplNest
