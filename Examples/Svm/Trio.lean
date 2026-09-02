import ProofForge

namespace Examples.Svm.Trio
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

/-- Fixed account handles are compile-time descriptors erased into the existing Runtime leaves. -/
@[pf_inline] def account0 : Account.Handle := Account.Handle.at 0
@[pf_inline] def account2 : Account.Handle := Account.Handle.at 2
@[pf_inline] def signer1 : Signer.Handle := Signer.Handle.at 1

@[pf_entry]
def lamports2 (_s : State) : UInt64 :=
  account2.lamports

@[pf_entry]
def dataLen2 (_s : State) : UInt64 :=
  account2.dataLen

@[pf_entry]
def signer2 (_s : State) : UInt64 :=
  account2.isSigner

@[pf_entry]
def writable2 (_s : State) : UInt64 :=
  account2.isWritable

@[pf_entry]
def executable2 (_s : State) : UInt64 :=
  account2.isExecutable

@[pf_entry]
def key20 (_s : State) : UInt64 :=
  account2.keyWord 0

/-- 账户 1 必须是 signer。 -/
@[pf_entry]
def needSig1 (_s : State) : UInt64 :=
  signer1.key0

/-- 账户 0 owner 是否是当前 program。期望 0。 -/
@[pf_entry]
def self0 (_s : State) : UInt64 :=
  account0.ownedBySelf

/-- 账户 2 owner 是否是当前 program。异 owner 期望 1。 -/
@[pf_entry]
def self2 (_s : State) : UInt64 :=
  account2.ownedBySelf

end Examples.Svm.Trio