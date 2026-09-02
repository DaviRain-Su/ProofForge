import ProofForge

namespace Examples.Near.NearFtReceiverValue
structure State where
  calls : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

open ProofForge.Wasm.Near.Runtime

@[pf_entry] def init : State := { calls := 0 }
@[pf_entry] def get (state : State) : UInt64 := state.calls

/-- Standards-shaped immediate-value receiver boundary. Returning the complete amount means this
closed fixture rejects every transfer. Input remains ProofForge's bounded canonical JSON subset. -/
@[pf_entry]
def ft_on_transfer (state : State) (args : FtOnTransferArgs) :
    Except Error (State × ProofForge.Core.Value.UInt128) :=
  if state.calls < 18446744073709551615 then
    .ok ({ calls := state.calls + 1 }, ⟨args.amount.w0, args.amount.w1⟩)
  else .error .overflow

end Examples.Near.NearFtReceiverValue