import ProofForge.Evm.Sdk

namespace Examples.EvmCtx

open ProofForge.Evm.Sdk

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

inductive TaggedRequest where
  | idle
  | one (value : UInt64)
  | pair (left right : UInt64)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- view：`CALLER` 低 8 字节。不是 `signerKey0`，也不是完整 address。 -/
@[pf_entry]
def caller (_s : State) : UInt64 :=
  Context.callerLow

/-- view：`NUMBER`。不是 `clockSlot`。 -/
@[pf_entry]
def height (_s : State) : UInt64 :=
  Context.blockNumber

/-- Full-width `GAS` observation. All four limbs come from one cached opcode result. -/
@[pf_entry]
def gasLeft (_s : State) : UInt256 :=
  Context.gasLeft

/-- 把当前 block number 写入 dummy。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := Context.blockNumber }, Context.blockNumber)
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

/-- EVM Tagged Tuple v1 binds an ordinary Option to `(bool,uint64)`. `false` requires a zero
payload word, so there is one canonical ABI encoding for `none`. -/
@[pf_entry]
def optionValue (_s : State) (value : Option UInt64) : UInt64 :=
  match value with
  | none => 5
  | some amount => amount + 1

/-- Payload enums use `(uint8,uint64,uint64)` with constructor ordinals and zero inactive lanes.
This is an EVM ABI policy, not the branch-dependent Borsh representation used by SVM. -/
@[pf_entry]
def taggedValue (_s : State) (request : TaggedRequest) : UInt64 :=
  match request with
  | .idle => 3
  | .one value => value + 10
  | .pair left right => left + right

/-- Tagged results reuse the fixed shared source frame, while the output codec independently
rebuilds and validates canonical Tagged Tuple v1 returndata. -/
@[pf_entry]
def echoOptionValue (_s : State) (value : Option UInt64) : Option UInt64 := value

@[pf_entry]
def echoTaggedValue (_s : State) (value : TaggedRequest) : TaggedRequest := value

end Examples.EvmCtx
