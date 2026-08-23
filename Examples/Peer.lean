import ProofForge

namespace Examples.Peer

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

/-- 无参 mutate 占入口；不写业务槽。 -/
@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

@[pf_entry]
def lamports1 (_s : State) : UInt64 :=
  accLamports1

@[pf_entry]
def owner1 (_s : State) : UInt64 :=
  accOwner1

@[pf_entry]
def dataLen1 (_s : State) : UInt64 :=
  accDataLen1

/-- 读旗，不强制入口签名。 -/
@[pf_entry]
def signer1 (_s : State) : UInt64 :=
  isSigner1

@[pf_entry]
def writable1 (_s : State) : UInt64 :=
  isWritable1

@[pf_entry]
def executable1 (_s : State) : UInt64 :=
  isExecutable1

end Examples.Peer
