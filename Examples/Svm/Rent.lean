import ProofForge

namespace Examples.Svm.Rent
open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 16 字节账户的 rent-exempt 下限。 -/
@[pf_entry]
def exempt (_s : State) : UInt64 :=
  Sysvar.Rent.minimumBalance 16

/-- 把 exemption 写进状态。`0 ≠ 1` 给无参 mutate 一条比较守卫。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := Sysvar.Rent.minimumBalance 16 }, Sysvar.Rent.minimumBalance 16)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

end Examples.Svm.Rent