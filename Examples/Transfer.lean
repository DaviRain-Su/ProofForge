import ProofForge

namespace Examples.Transfer

open ProofForge.Runtime

/-- 无链上状态；init 只占入口形状。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 封闭 system.transfer。账户表由 `invoke` 钉死，不进 Lean 参数。 -/
@[pf_entry]
def transfer (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemTransfer lamports
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Transfer
