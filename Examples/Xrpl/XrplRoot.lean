import ProofForge

/-!
Stamp the caller's AccountRoot Sequence / Flags / OwnerCount into JSON.
AlphaNet host: accountroot_id + cache_le + le_field. Zero-arg for public RPC.
OwnerCount is the cache_le snapshot (creating ContractData may bump the live count).
-/
namespace Examples.Xrpl.XrplRoot
open ProofForge.Wasm.Xrpl.Sdk

structure State where
  seq : UInt64
  flags : UInt64
  ownc : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { seq := 0, flags := 0, ownc := 0 }

@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ seq := Context.callerSequence
           flags := Context.callerFlags
           ownc := Context.callerOwnerCount }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def getSeq (s : State) : UInt64 :=
  s.seq

end Examples.Xrpl.XrplRoot