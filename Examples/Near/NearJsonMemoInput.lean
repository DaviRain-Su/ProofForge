import ProofForge

namespace Examples.Near.NearJsonMemoInput
structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init (marker : UInt64) : State := { marker }
@[pf_entry] def get (state : State) : UInt64 := state.marker

/-! Codec diagnostics only; these are not public FT methods. -/
@[pf_entry] def memoPresent (_state : State) (memo : OptionalMemo16) : UInt64 := memo.present
@[pf_entry] def memoLength (_state : State) (memo : OptionalMemo16) : UInt64 := memo.length
@[pf_entry] def memoW0 (_state : State) (memo : OptionalMemo16) : UInt64 := memo.w0
@[pf_entry] def memoW1 (_state : State) (memo : OptionalMemo16) : UInt64 := memo.w1
@[pf_entry] def commitLength (_state : State) (memo : OptionalMemo16) : Except Error (State × UInt64) :=
  .ok ({ marker := memo.length }, memo.length)

end Examples.Near.NearJsonMemoInput