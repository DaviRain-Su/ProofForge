import ProofForge

namespace Examples.VaultRentGrow

open ProofForge.Svm.Sdk

/--
`svm-sdk-001` consumer B: grow a program-owned vault after an explicit rent top-up funded by a
second program-owned account. Physical layout mirrors the lamport fixtures (state 0, vault 1,
fund 2) so Mollusk can reuse the three-account harness pattern.
-/
structure State where
  grown : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def vault : Account.Handle := Account.Handle.at 1
@[pf_inline] def fund : Account.Handle := Account.Handle.at 2

def targetLen : Nat := 64

@[pf_entry]
def init (initial : UInt64) : State :=
  { grown := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.grown

/-- Grow the vault to 64 bytes with rent top-up from `fund`, then record success in state. -/
@[pf_entry]
def grow (s : State) : Except Error (State × UInt64) :=
  if s.grown < ~~~(0 : UInt64) then
    let deficit := vault.topUpRentExempt fund 64
    let _ := deficit
    let _ := vault.resizeData (64 : UInt64)
    let next := s.grown + 1
    .ok ({ grown := next }, vault.dataLen)
  else
    .error .overflow

end Examples.VaultRentGrow
