import ProofForge

namespace Examples.Svm.SysXfer
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

/-- TransferWithSeed；此应用选择 `"vault"`。 -/
@[pf_entry]
def sendSeed (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.transfer "vault" lamports
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Svm.SysXfer