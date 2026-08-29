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

/-- view：本合约余额（u128 截断到 UInt64）。 -/
@[pf_entry]
def selfBal (_s : State) : UInt64 :=
  Context.balanceOfSelf

/-- 把当前 height 写入状态。`0 ≠ 1` 给无参 mutate 一条比较守卫。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.blockHeight }, Context.blockHeight)
  else
    .error .overflow

/-- 付款入口：要求 attached deposit 的 lo64，hi64≠0 由 runtime trap。 -/
@[pf_entry]
def takeDeposit (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.attachedDeposit }, Context.attachedDeposit)
  else
    .error .overflow

/-- 入口：读 predecessor 前 8 字节。view 禁止。 -/
@[pf_entry]
def pingCaller (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.caller }, Context.caller)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

end Examples.NearCtx
