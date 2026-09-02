import ProofForge

namespace Examples.Near.NearJsonFtTransferCallInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Parser diagnostics only: no token mutation, Promise, or standard method export. -/
@[pf_entry] def receiverLength (_state : State) (args : FtTransferCallArgs) : UInt64 :=
  args.receiverId.length
@[pf_entry] def receiverW0 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.receiverId.w0
@[pf_entry] def receiverW7 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.receiverId.w7
@[pf_entry] def amountW0 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.amount.w0
@[pf_entry] def amountW1 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.amount.w1
@[pf_entry] def memoPresent (_state : State) (args : FtTransferCallArgs) : UInt64 := args.memo.present
@[pf_entry] def memoLength (_state : State) (args : FtTransferCallArgs) : UInt64 := args.memo.length
@[pf_entry] def memoW1 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.memo.w1
@[pf_entry] def messageLength (_state : State) (args : FtTransferCallArgs) : UInt64 := args.msg.length
@[pf_entry] def messageW0 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.msg.w0
@[pf_entry] def messageW7 (_state : State) (args : FtTransferCallArgs) : UInt64 := args.msg.w7
@[pf_entry] def commitMessageLength (_state : State) (args : FtTransferCallArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.msg.length }, args.amount.w1)

end Examples.Near.NearJsonFtTransferCallInput