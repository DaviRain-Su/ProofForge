import ProofForge

namespace Examples.SysAlloc

open ProofForge.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给账户 0 开 16 字节。 -/
@[pf_entry]
def alloc (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemAllocate 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

/-- 把账户 0 的 owner 改成当前 program。 -/
@[pf_entry]
def assign (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemAssign
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.SysAlloc
