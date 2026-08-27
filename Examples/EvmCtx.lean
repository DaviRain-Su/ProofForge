import ProofForge

namespace Examples.EvmCtx

open ProofForge.Evm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

structure AggregateMeta where
  side : UInt8
  enabled : Bool

structure AggregateRequest where
  amount : UInt64
  details : AggregateMeta

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- view：`CALLER` 低 8 字节。不是 `signerKey0`，也不是完整 address。 -/
@[pf_entry]
def caller (_s : State) : UInt64 :=
  evmCaller

/-- view：`NUMBER`。不是 `clockSlot`。 -/
@[pf_entry]
def height (_s : State) : UInt64 :=
  evmBlockNumber

/-- 把当前 block number 写入 dummy。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := evmBlockNumber }, evmBlockNumber)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.dummy

/-- Static records, products, and literal vectors remain logical Lean values at the source. The
EVM adapter independently binds their scalar leaves to canonical ABI words. -/
@[pf_entry]
def aggregate (_s : State) (request : AggregateRequest) (pair : UInt32 × UInt64)
    (levels : Vector UInt16 3) : UInt64 × Bool :=
  (request.amount + request.details.side.toUInt64 +
    (if request.details.enabled then (1 : UInt64) else 0) +
    pair.1.toUInt64 + pair.2 + levels[0].toUInt64 + levels[2].toUInt64,
   request.details.enabled)

end Examples.EvmCtx
