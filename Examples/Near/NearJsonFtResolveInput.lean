import ProofForge

namespace Examples.Near.NearJsonFtResolveInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Resolver-argument parser diagnostics only. No Promise result or ledger policy is present. -/
@[pf_entry] def senderLength (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.length
@[pf_entry] def senderW0 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w0
@[pf_entry] def senderW1 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w1
@[pf_entry] def senderW2 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w2
@[pf_entry] def senderW3 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w3
@[pf_entry] def senderW4 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w4
@[pf_entry] def senderW5 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w5
@[pf_entry] def senderW6 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w6
@[pf_entry] def senderW7 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.senderId.w7
@[pf_entry] def receiverLength (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.length
@[pf_entry] def receiverW0 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w0
@[pf_entry] def receiverW1 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w1
@[pf_entry] def receiverW2 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w2
@[pf_entry] def receiverW3 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w3
@[pf_entry] def receiverW4 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w4
@[pf_entry] def receiverW5 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w5
@[pf_entry] def receiverW6 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w6
@[pf_entry] def receiverW7 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.receiverId.w7
@[pf_entry] def amountW0 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.amount.w0
@[pf_entry] def amountW1 (_state : State) (args : FtResolveTransferArgs) : UInt64 := args.amount.w1

@[pf_entry] def commitAmountHigh (_state : State) (args : FtResolveTransferArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.amount.w1 }, args.amount.w1)

end Examples.Near.NearJsonFtResolveInput