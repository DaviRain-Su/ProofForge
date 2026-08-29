import ProofForge

/-!
Stamp the current ContractCall Flags. Zero-arg. Completes the tx_field UInt32
surface next to Sequence / Fee.
-/
namespace Examples.XrplFlag

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  flags : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { flags := 0 }

@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ flags := Context.txFlags }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.flags

end Examples.XrplFlag
