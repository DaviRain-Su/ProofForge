import ProofForge

namespace Examples.Signed

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

/-- PDA 用 `"vault"` + canonical bump 给自己签字，CPI 进账户 1。 -/
@[pf_entry]
def signed (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := invokeSigned 1 #[{ acc := 0, signer := true }] #[] "vault" (findPda "vault")
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

/-- 同一条种子，bump 钉死 0。syscall 必须失败。 -/
@[pf_entry]
def badBump (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := invokeSigned 1 #[{ acc := 0, signer := true }] #[] "vault" 0
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Signed
