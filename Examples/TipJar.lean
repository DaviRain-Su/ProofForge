import SolanaLean

namespace Examples.TipJar

open SolanaLean.Runtime

/-- 无链上业务状态；init 只占入口形状。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- `eq(callvalue(), amt)`。入口因此 payable。不是 `systemTransfer`。 -/
@[solana_entry]
def deposit (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmDeposit amt)
  else
    .error .overflow

/-- value CALL 到 20B（三叶 Addr20）。失败 revert。重入不进参考语义。 -/
@[solana_entry]
def payout (_s : State) (w0 w1 w2 amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmSendEth w0 w1 w2 amt)
  else
    .error .overflow

/-- LOG1 `Tipped(uint64)`。 -/
@[solana_entry]
def logTip (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmLogTipped amt)
  else
    .error .overflow

@[solana_entry]
def chainId (_s : State) : UInt64 :=
  evmChainId

@[solana_entry]
def timestamp (_s : State) : UInt64 :=
  evmTimestamp

/-- `ADDRESS` 低 8 字节。完整 20B 用 `selfW*`。 -/
@[solana_entry]
def selfLow (_s : State) : UInt64 :=
  evmSelf

@[solana_entry]
def selfBal (_s : State) : UInt64 :=
  evmSelfBalance

/-- view：`STATICCALL` 下恒为 0。 -/
@[solana_entry]
def callValue (_s : State) : UInt64 :=
  evmCallValue

@[solana_entry]
def callerW0 (_s : State) : UInt64 :=
  evmCallerW0

@[solana_entry]
def callerW1 (_s : State) : UInt64 :=
  evmCallerW1

@[solana_entry]
def callerW2 (_s : State) : UInt64 :=
  evmCallerW2

@[solana_entry]
def selfW0 (_s : State) : UInt64 :=
  evmSelfW0

@[solana_entry]
def selfW1 (_s : State) : UInt64 :=
  evmSelfW1

@[solana_entry]
def selfW2 (_s : State) : UInt64 :=
  evmSelfW2

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TipJar
