import ProofForge

namespace Examples.NearJsonAccountInput

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  .ok ({ marker := 1 }, 1)

/-! These view-only projections exercise the compiler-owned bounded AccountId JSON object input.
They are a codec fixture, not public NEP-141 methods or a generic JSON ABI. -/

@[pf_entry] def accountLength (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.length
@[pf_entry] def accountW0 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w0
@[pf_entry] def accountW1 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w1
@[pf_entry] def accountW2 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w2
@[pf_entry] def accountW3 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w3
@[pf_entry] def accountW4 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w4
@[pf_entry] def accountW5 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w5
@[pf_entry] def accountW6 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w6
@[pf_entry] def accountW7 (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 := account.w7

end Examples.NearJsonAccountInput
