import ProofForge

namespace Examples.Near.NearJsonFtTransferInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Parser diagnostics only. No method in this fixture transfers tokens or uses a standard name. -/
@[pf_entry] def inspectReceiverLength (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.length
@[pf_entry] def inspectReceiverW0 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w0
@[pf_entry] def inspectReceiverW1 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w1
@[pf_entry] def inspectReceiverW2 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w2
@[pf_entry] def inspectReceiverW3 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w3
@[pf_entry] def inspectReceiverW4 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w4
@[pf_entry] def inspectReceiverW5 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w5
@[pf_entry] def inspectReceiverW6 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w6
@[pf_entry] def inspectReceiverW7 (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.receiverId.w7
@[pf_entry] def inspectAmountW0 (_state : State) (args : FtTransferArgs) : UInt64 := args.amount.w0
@[pf_entry] def inspectAmountW1 (_state : State) (args : FtTransferArgs) : UInt64 := args.amount.w1
@[pf_entry] def inspectMemoPresent (_state : State) (args : FtTransferArgs) : UInt64 :=
  args.memo.present
@[pf_entry] def inspectMemoLength (_state : State) (args : FtTransferArgs) : UInt64 := args.memo.length
@[pf_entry] def inspectMemoW0 (_state : State) (args : FtTransferArgs) : UInt64 := args.memo.w0
@[pf_entry] def inspectMemoW1 (_state : State) (args : FtTransferArgs) : UInt64 := args.memo.w1
@[pf_entry] def commitMemoLength (_state : State) (args : FtTransferArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.memo.length }, args.amount.w1)

end Examples.Near.NearJsonFtTransferInput