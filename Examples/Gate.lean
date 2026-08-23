import ProofForge

namespace Examples.Gate

open ProofForge.Svm.Runtime

structure State where
  open_ : Bool
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { open_ := false, dummy := 0 }

@[pf_entry]
def openGate (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ open_ := true, dummy := 0 }, 1)
  else
    .error .overflow

@[pf_entry]
def closeGate (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ open_ := false, dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def isOpen (s : State) : UInt64 :=
  if s.open_ then 1 else 0

@[pf_entry]
def now (_s : State) : UInt64 :=
  unixTime

end Examples.Gate
