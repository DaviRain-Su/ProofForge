import ProofForge

/-!
Local 2.6.1: `Pay.emitToCaller` → `build_txn` / `add_txn_field` / `emit_built_txn`
Payment of 192 drops to the caller. Public AlphaNet is tefBAD_AUTH -196.
Not Sdk.Payments, not a Map.
-/
namespace Examples.XrplEmit

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Emit 192 drops from the funded contract pseudo-account to the caller.
Zero wasm params: local 2.6.1 cannot sign Function.ParameterType. -/
@[pf_entry]
def ping (s : State) : Except Error (State × UInt64) :=
  if Pay.emitToCaller ≤ u64Max then
    .ok ({ bal := s.bal + (0 : UInt64) }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplEmit
