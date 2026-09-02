import ProofForge

namespace Examples.Xrpl.XrplCtx
open ProofForge.Wasm.Xrpl.Sdk

structure State where
  stamped : UInt64
  callerLo : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { stamped := 0, callerLo := 0 }

/-- view：当前账本序号。不是 `clockSlot`。 -/
@[pf_entry]
def height (_s : State) : UInt64 :=
  Context.ledgerSqn

/-- view：caller 低 8 字节。不是身份，也不是 `evmCaller`。 -/
@[pf_entry]
def key0 (_s : State) : UInt64 :=
  Context.callerLo

/-- 把当前序号和 caller 低 8 字节写入状态。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.ledgerSqn, callerLo := Context.callerLo }, Context.ledgerSqn)
  else
    .error .overflow

end Examples.Xrpl.XrplCtx