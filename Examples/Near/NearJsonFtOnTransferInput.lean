import ProofForge

namespace Examples.Near.NearJsonFtOnTransferInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Receiver-argument parser diagnostics only. No standard export, receiver policy, or Promise. -/
@[pf_entry] def senderLength (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.length
@[pf_entry] def senderW0 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w0
@[pf_entry] def senderW1 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w1
@[pf_entry] def senderW2 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w2
@[pf_entry] def senderW3 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w3
@[pf_entry] def senderW4 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w4
@[pf_entry] def senderW5 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w5
@[pf_entry] def senderW6 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w6
@[pf_entry] def senderW7 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.senderId.w7
@[pf_entry] def amountW0 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.amount.w0
@[pf_entry] def amountW1 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.amount.w1
@[pf_entry] def messageLength (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.length
@[pf_entry] def messageW0 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w0
@[pf_entry] def messageW1 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w1
@[pf_entry] def messageW2 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w2
@[pf_entry] def messageW3 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w3
@[pf_entry] def messageW4 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w4
@[pf_entry] def messageW5 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w5
@[pf_entry] def messageW6 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w6
@[pf_entry] def messageW7 (_state : State) (args : FtOnTransferArgs) : UInt64 := args.msg.w7

@[pf_entry] def commitAmountHigh (_state : State) (args : FtOnTransferArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.amount.w1 }, args.amount.w1)

end Examples.Near.NearJsonFtOnTransferInput