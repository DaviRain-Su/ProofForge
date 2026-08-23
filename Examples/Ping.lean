import ProofForge

namespace Examples.Ping

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

/-- CPI 到外层账户 1。program id 来自该账户 key。 -/
@[pf_entry]
def ping (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := invokeAcc1
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Ping
