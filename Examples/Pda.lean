import ProofForge

namespace Examples.Pda

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

/-- 无参 mutate 占入口。 -/
@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

/-- 当前 program id + 字面量种子 `"vault"` 的 canonical bump。 -/
@[pf_entry]
def bump (_s : State) : UInt64 :=
  findPda "vault"

/-- `"vault"` + canonical bump 是否合法 PDA。成功 0。 -/
@[pf_entry]
def check (_s : State) : UInt64 :=
  checkPda "vault" (findPda "vault")

/-- `"vault"` + bump 0。必须失败，返回 1。 -/
@[pf_entry]
def checkBad (_s : State) : UInt64 :=
  checkPda "vault" 0

end Examples.Pda
