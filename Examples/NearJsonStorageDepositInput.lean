import ProofForge

namespace Examples.NearJsonStorageDepositInput

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Parser diagnostics only. This fixture does not register accounts or export `storage_deposit`. -/
@[pf_entry] def inspectAccountPresent (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountPresent
@[pf_entry] def inspectAccountLength (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.length
@[pf_entry] def inspectAccountW0 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w0
@[pf_entry] def inspectAccountW1 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w1
@[pf_entry] def inspectAccountW2 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w2
@[pf_entry] def inspectAccountW3 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w3
@[pf_entry] def inspectAccountW4 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w4
@[pf_entry] def inspectAccountW5 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w5
@[pf_entry] def inspectAccountW6 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w6
@[pf_entry] def inspectAccountW7 (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.accountId.w7
@[pf_entry] def inspectRegistrationOnly (_state : State) (args : StorageDepositArgs) : UInt64 :=
  args.registrationOnly
@[pf_entry] def commitRegistrationOnly (_state : State) (args : StorageDepositArgs) :
    Except Error (State × UInt64) :=
  .ok ({ marker := args.registrationOnly }, args.registrationOnly)

end Examples.NearJsonStorageDepositInput
