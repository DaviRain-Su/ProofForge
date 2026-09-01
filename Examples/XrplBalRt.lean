import ProofForge

/-!
Stamp the caller's XRP AccountRoot.Balance (drops) into JSON slot `drops`.
AlphaNet host: accountroot_id + cache_le + le_field. Zero-arg for public RPC.
-/
namespace Examples.XrplBalRt

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  drops : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { drops := 0 }

@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ drops := Context.callerBalanceDrops }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.drops

end Examples.XrplBalRt
