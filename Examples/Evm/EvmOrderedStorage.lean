import ProofForge.Evm.Sdk

/-!
Minimal consumer for ordered static-storage effects. It demonstrates the exact boundary needed by
call-order-sensitive policies: a typed static handle stores before and after an external CALL,
while the ordinary returned Lean state remains a separate final-writeback contract.
-/

namespace Examples.Evm.EvmOrderedStorage
open ProofForge.Evm.Sdk

structure State where
  status : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  status : Storage.Static.Handle UInt64

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let status := Storage.Static.Layout.root.uint64 "status"
  { handle := { status := status.handle }, next := status.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | locked
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { status := 1 }

/-- One immediate write. The chain result is `value`; the pure host stub leaves `s` unchanged. -/
@[pf_entry]
def writeNow (s : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok (s, declared.handle.status.storeNow value)

/--
Store entered status, perform the bounded ETH CALL, then restore not-entered status. The three
effects must remain in this lexical order; a failed CALL reverts the whole EVM transaction.
-/
@[pf_entry]
def writeAroundSend (s : State) (destination : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if Reentrancy.canEnter s.status then
    let _ := Reentrancy.enter declared.handle.status
    let _ := Ether.send destination amount
    .ok (s, Reentrancy.leave declared.handle.status)
  else
    .error .locked

@[pf_entry]
def statusOf (s : State) : UInt64 := s.status

end Examples.Evm.EvmOrderedStorage