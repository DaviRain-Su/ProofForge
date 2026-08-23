import ProofForge

namespace Examples.Create

open ProofForge.Svm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给账户 1 开 16 字节、owner = 当前 program。 -/
@[pf_entry]
def create (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemCreate lamports 16
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Create
