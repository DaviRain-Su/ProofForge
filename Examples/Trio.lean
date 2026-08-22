import ProofForge

namespace Examples.Trio

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

@[pf_entry]
def lamports2 (_s : State) : UInt64 :=
  accLamports 2

@[pf_entry]
def dataLen2 (_s : State) : UInt64 :=
  accDataLen 2

@[pf_entry]
def signer2 (_s : State) : UInt64 :=
  isSigner 2

@[pf_entry]
def writable2 (_s : State) : UInt64 :=
  isWritable 2

@[pf_entry]
def executable2 (_s : State) : UInt64 :=
  isExecutable 2

@[pf_entry]
def key20 (_s : State) : UInt64 :=
  accKeyWord 2 0

/-- 账户 1 必须是 signer。 -/
@[pf_entry]
def needSig1 (_s : State) : UInt64 :=
  signerKey 1

/-- 账户 0 owner 是否是当前 program。期望 0。 -/
@[pf_entry]
def self0 (_s : State) : UInt64 :=
  ownerIsSelf 0

/-- 账户 2 owner 是否是当前 program。异 owner 期望 1。 -/
@[pf_entry]
def self2 (_s : State) : UInt64 :=
  ownerIsSelf 2

end Examples.Trio
