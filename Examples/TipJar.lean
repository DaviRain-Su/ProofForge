import ProofForge

namespace Examples.TipJar

open ProofForge.Evm.Runtime

/-- 无链上业务状态；init 只占入口形状。 -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- `eq(callvalue(), packed uint256)`。入口因此 payable。不是 `systemTransfer`。 -/
@[pf_entry]
def deposit (_s : State) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmDeposit256 amt)
  else
    .error .overflow

/-- value CALL 到 20B Addr20，金额是 packed wei。失败 revert。重入不进参考语义。 -/
@[pf_entry]
def payout (_s : State) (dst : Addr20) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmSendEth256 dst amt)
  else
    .error .overflow

/-- LOG1 `Tipped(uint64)`。 -/
@[pf_entry]
def logTip (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmLogTipped amt)
  else
    .error .overflow

/-- 无 calldata 的 payable `receive()`。 -/
@[pf_entry]
def receive (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, evmReceive)
  else
    .error .overflow

@[pf_entry]
def chainId (_s : State) : UInt64 :=
  evmChainId

@[pf_entry]
def timestamp (_s : State) : UInt64 :=
  evmTimestamp

/-- `ADDRESS` 低 8 字节。完整 20B 用 `self20`。 -/
@[pf_entry]
def selfLow (_s : State) : UInt64 :=
  evmSelf

@[pf_entry]
def selfBal (_s : State) : UInt256 :=
  evmSelfBalance256

/-- view：`STATICCALL` 下恒为 0。完整 wei。 -/
@[pf_entry]
def callValue (_s : State) : UInt256 :=
  evmCallValue256

@[pf_entry]
def caller20 (_s : State) : Addr20 :=
  evmCaller20

@[pf_entry]
def self20 (_s : State) : Addr20 :=
  evmSelf20

@[pf_entry]
def callerW0 (_s : State) : UInt64 :=
  evmCallerW0

@[pf_entry]
def callerW1 (_s : State) : UInt64 :=
  evmCallerW1

@[pf_entry]
def callerW2 (_s : State) : UInt64 :=
  evmCallerW2

@[pf_entry]
def selfW0 (_s : State) : UInt64 :=
  evmSelfW0

@[pf_entry]
def selfW1 (_s : State) : UInt64 :=
  evmSelfW1

@[pf_entry]
def selfW2 (_s : State) : UInt64 :=
  evmSelfW2

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.TipJar
