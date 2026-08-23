import ProofForge

namespace Examples.EvmCtx

open ProofForge.Evm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

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

end Examples.EvmCtx
