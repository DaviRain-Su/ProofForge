import SolanaLean

namespace Examples.Info

open SolanaLean.Runtime

/-- 无业务状态；init 只占入口形状。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 无参 mutate 占入口；不写业务槽。 -/
@[solana_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

@[solana_entry]
def lamports (_s : State) : UInt64 :=
  accLamports0

@[solana_entry]
def owner0 (_s : State) : UInt64 :=
  accOwner0

@[solana_entry]
def dataLen (_s : State) : UInt64 :=
  accDataLen0

@[solana_entry]
def nacc (_s : State) : UInt64 :=
  accN

/-- 读旗，不强制入口签名。 -/
@[solana_entry]
def signer (_s : State) : UInt64 :=
  isSigner0

@[solana_entry]
def writable (_s : State) : UInt64 :=
  isWritable0

@[solana_entry]
def executable (_s : State) : UInt64 :=
  isExecutable0

end Examples.Info
