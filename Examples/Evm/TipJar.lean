import ProofForge.Evm.Sdk

namespace Examples.Evm.TipJar
open ProofForge.Evm.Sdk

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
    .ok ({ dummy := 0 }, Ether.accept amt)
  else
    .error .overflow

/-- value CALL 到 20B Address，金额是 packed wei。失败 revert。重入不进参考语义。 -/
@[pf_entry]
def payout (_s : State) (dst : Address) (amt : UInt256) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, Ether.send dst amt)
  else
    .error .overflow

/-- LOG1 `Tipped(uint64)`。 -/
@[pf_entry]
def logTip (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, Event.tipped amt)
  else
    .error .overflow

/-- 无 calldata 的 payable `receive()`。 -/
@[pf_entry]
def receive (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, Ether.receive)
  else
    .error .overflow

@[pf_entry]
def chainId (_s : State) : UInt64 :=
  Context.chainId

@[pf_entry]
def timestamp (_s : State) : UInt64 :=
  Context.timestamp

@[pf_entry]
def baseFee (_s : State) : UInt256 :=
  Context.baseFee

@[pf_entry]
def prevRandao (_s : State) : UInt256 :=
  Context.prevRandao

@[pf_entry]
def gasLimit (_s : State) : UInt256 :=
  Context.gasLimit

/-- Full block beneficiary address. -/
@[pf_entry]
def coinbase (_s : State) : Address :=
  Context.coinbase

/-- `ADDRESS` 低 8 字节。完整 20B 用 `self20`。 -/
@[pf_entry]
def selfLow (_s : State) : UInt64 :=
  Context.selfLow

@[pf_entry]
def selfBal (_s : State) : UInt256 :=
  Context.selfBalance

/-- view：`STATICCALL` 下恒为 0。完整 wei。 -/
@[pf_entry]
def callValue (_s : State) : UInt256 :=
  Context.callValue

@[pf_entry]
def caller20 (_s : State) : Address :=
  Context.caller

@[pf_entry]
def self20 (_s : State) : Address :=
  Context.self

@[pf_entry]
def callerW0 (_s : State) : UInt64 :=
  Context.caller.w0

@[pf_entry]
def callerW1 (_s : State) : UInt64 :=
  Context.caller.w1

@[pf_entry]
def callerW2 (_s : State) : UInt64 :=
  Context.caller.w2

@[pf_entry]
def selfW0 (_s : State) : UInt64 :=
  Context.self.w0

@[pf_entry]
def selfW1 (_s : State) : UInt64 :=
  Context.self.w1

@[pf_entry]
def selfW2 (_s : State) : UInt64 :=
  Context.self.w2

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Evm.TipJar