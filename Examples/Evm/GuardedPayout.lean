import ProofForge.Evm.Sdk

/-!
Application-owned payout consumer for the reusable EVM SDK reentrancy policy. The SDK owns the
lock sentinels and ordered handle writes; this contract owns its payout, account destination, and
typed rejection terminal.
-/

namespace Examples.Evm.GuardedPayout
open ProofForge.Evm.Sdk

structure State where
  guard : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  guard : Storage.Static.Handle UInt64

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let guard := Storage.Static.Layout.root.uint64 "guard"
  { handle := { guard := guard.handle }, next := guard.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | reentrantCall
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { guard := Reentrancy.notEntered }

/-- Enter lock → bounded ETH CALL → leave lock. A failed CALL rolls back the entered write. -/
@[pf_entry]
def payout (s : State) (destination : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if Reentrancy.canEnter s.guard then
    let _ := Reentrancy.enter declared.handle.guard
    let _ := Ether.send destination amount
    .ok (s, Reentrancy.leave declared.handle.guard)
  else
    .error .reentrantCall

@[pf_entry]
def statusOf (s : State) : UInt64 := s.guard

end Examples.Evm.GuardedPayout