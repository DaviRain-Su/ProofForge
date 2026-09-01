import ProofForge

/-!
Stamp a compile-time other AccountID's XRP Balance (drops) onto the caller's
card. Persist owner stays the caller. Destination is the second-wallet fixture.
-/
namespace Examples.XrplPeer

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
    .ok ({ drops := Context.litBalanceDrops "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350" },
         (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.drops

end Examples.XrplPeer
