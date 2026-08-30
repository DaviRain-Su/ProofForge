import ProofForge

/-!
AlphaNet public RPC 502s any `ContractCall` that carries `Parameters`.
This contract has no function parameters: `initialize` writes 0, `bump`
adds 1. Host table still comes from `--target xrpl` vs `xrpl-alphanet`.
-/
namespace Examples.XrplSmoke

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- No arguments. Parameterized Call needs Function ABI on Create; empty ABI crashes the node. -/
@[pf_entry]
def init : State :=
  { value := 0 }

@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - 1 then
    .ok ({ value := s.value + 1 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.XrplSmoke
