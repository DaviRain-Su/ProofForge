import ProofForge

namespace Examples.Near.NearJsonStorageWithdrawInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Parser diagnostics only. This fixture does not withdraw storage, export `storage_withdraw`, or
schedule a refund. -/
@[pf_entry] def amountPresent (_state : State) (args : StorageWithdrawArgs) : UInt64 :=
  args.amountPresent

@[pf_entry] def amountW0 (_state : State) (args : StorageWithdrawArgs) : UInt64 :=
  args.amount.w0

@[pf_entry] def amountW1 (_state : State) (args : StorageWithdrawArgs) : UInt64 :=
  args.amount.w1

@[pf_entry] def commitW1 (_state : State) (args : StorageWithdrawArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.amount.w1 }, args.amount.w1)

end Examples.Near.NearJsonStorageWithdrawInput