import ProofForge

namespace Examples.RentTopUp

open ProofForge.Svm.Sdk

/--
`svm-sdk-001` consumer A: grow a program-owned data account after an explicit rent top-up from a
program-owned payer. State account 0 is authenticated ProofForge state; `dataAccount` is physical
account 1; `payer` is physical account 2. The target length is a compile-time constant (32 bytes).
-/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def dataAccount : Account.Handle := Account.Handle.at 1
@[pf_inline] def payer : Account.Handle := Account.Handle.at 2

/-- Target post-resize data length for the rent-aware grow entry. -/
def targetLen : Nat := 32

@[pf_entry]
def init (initial : UInt64) : State :=
  { dummy := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

/-- Top-up only: ensure `dataAccount` is rent-exempt for 32 bytes by debiting `payer`. -/
@[pf_entry]
def topUp (s : State) : Except Error (State × UInt64) :=
  if s.dummy < ~~~(0 : UInt64) then
    let deficit := dataAccount.topUpRentExempt payer 32
    .ok (s, deficit)
  else
    .error .overflow

/-- Resize to 32 bytes after an explicit rent top-up from `payer`; bump state and return length. -/
@[pf_entry]
def grow (s : State) : Except Error (State × UInt64) :=
  if s.dummy < ~~~(0 : UInt64) then
    let deficit := dataAccount.topUpRentExempt payer 32
    let _ := deficit
    let _ := dataAccount.resizeData (32 : UInt64)
    let next := s.dummy + 1
    .ok ({ dummy := next }, dataAccount.dataLen)
  else
    .error .overflow

end Examples.RentTopUp
