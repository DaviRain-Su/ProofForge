import ProofForge

namespace Examples.Xrpl.XrplRt2
open ProofForge.Wasm.Xrpl.Sdk

structure State where
  hashLo : UInt64
  fee : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { hashLo := 0, fee := 0 }

/-- 把 parent hash 低 8 字节和 base fee 写入槽。不是 `blockhash` / EVM `baseFee`。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ hashLo := Context.parentHashLo, fee := Context.baseFee }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def getHash (s : State) : UInt64 :=
  s.hashLo

@[pf_entry]
def getFee (s : State) : UInt64 :=
  s.fee

end Examples.Xrpl.XrplRt2