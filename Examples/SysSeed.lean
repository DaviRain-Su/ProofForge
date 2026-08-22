import SolanaLean

namespace Examples.SysSeed

open SolanaLean.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- AllocateWithSeed；种子钉死 `"vault"`，space 钉死 16。 -/
@[solana_entry]
def openSeed (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemAllocateWithSeed 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

/-- CreateAccountWithSeed；种子钉死 `"vault"`，space 钉死 16。 -/
@[solana_entry]
def createSeed (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemCreateWithSeed lamports 16
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

/-- AssignWithSeed；种子钉死 `"vault"`。 -/
@[solana_entry]
def assignSeed (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := systemAssignWithSeed
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.SysSeed
