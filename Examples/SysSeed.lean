import ProofForge

namespace Examples.SysSeed

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

/-- AllocateWithSeed；此应用选择 `"vault"`，space 钉死 16。 -/
@[pf_entry]
def openSeed (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.allocate "vault" 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

/-- CreateAccountWithSeed；此应用选择 `"vault"`，space 钉死 16。 -/
@[pf_entry]
def createSeed (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.createAccount "vault" lamports 16
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

/-- AssignWithSeed；此应用选择 `"vault"`。 -/
@[pf_entry]
def assignSeed (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.assign "vault"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.SysSeed
