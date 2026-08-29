import ProofForge

namespace Examples.NearCtx

open ProofForge.Wasm.Near.Sdk

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { stamped := 0 }

/-- view：当前 block height。不是 `clockSlot`，也不是 EVM `NUMBER`。 -/
@[pf_entry]
def height (_s : State) : UInt64 :=
  Context.blockHeight

/-- view：当前 unix 秒。host 是 `block_timestamp` ns÷10^9。 -/
@[pf_entry]
def seconds (_s : State) : UInt64 :=
  Context.unixTimeSeconds

/-- view：本合约完整 u128 余额的低 64 位；不会因高位非零而 trap。 -/
@[pf_entry]
def selfBal (_s : State) : UInt64 :=
  Context.balanceOfSelf.w0

/-- view：本合约完整 u128 余额的高 64 位。 -/
@[pf_entry]
def selfBalHigh (_s : State) : UInt64 :=
  Context.balanceOfSelf.w1

/-- view：本账户 id 前 8 字节 LE；完整身份用 `Context.self`。 -/
@[pf_entry]
def selfId (_s : State) : UInt64 :=
  Context.selfLo

/-- view：完整 AccountId 的实际 UTF-8 字节数。 -/
@[pf_entry]
def selfIdLength (_s : State) : UInt64 :=
  Context.self.length

/-- view：本账户 id 的 UTF-8 字节 8..15，小端并零填充。 -/
@[pf_entry]
def selfIdWord1 (_s : State) : UInt64 :=
  Context.self.w1

/-- 把当前 height 写入状态。`0 ≠ 1` 给无参 mutate 一条比较守卫。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.blockHeight }, Context.blockHeight)
  else
    .error .overflow

/-- 付款入口：读取完整 attached deposit 的低 64 位；高位非零仍是有效金额。 -/
@[pf_entry]
def takeDeposit (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.attachedDeposit.w0 }, Context.attachedDeposit.w0)
  else
    .error .overflow

/-- 付款入口：读取完整 attached deposit 的高 64 位。 -/
@[pf_entry]
def takeDepositHigh (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.attachedDeposit.w1 }, Context.attachedDeposit.w1)
  else
    .error .overflow

/-- 显式旧接口：attached deposit 超过 UInt64 时保留历史 overflow trap。 -/
@[pf_entry]
def takeDepositLegacy (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.attachedDepositLo }, Context.attachedDepositLo)
  else
    .error .overflow

/-- 入口：读 predecessor 前 8 字节。view 禁止。 -/
@[pf_entry]
def pingCaller (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.callerLo }, Context.callerLo)
  else
    .error .overflow

/-- 回调鉴权基础：直接调用本合约时 predecessor 与 current account 完整相等。 -/
@[pf_entry]
def checkSelfCall (_s : State) : Except Error (State × UInt64) :=
  if Access.isSelfCall then
    .ok ({ stamped := 1 }, 1)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

end Examples.NearCtx
