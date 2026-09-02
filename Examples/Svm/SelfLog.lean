import ProofForge

namespace Examples.Svm.SelfLog
open ProofForge.Svm.Runtime

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (seed : UInt64) : State :=
  { value := seed }

/--
Emit a signed raw self-CPI whose first byte selects tag 15. The remaining packed words model
an opaque Borsh payload: the raw handler authenticates the `"log"` PDA and deliberately leaves
payload interpretation to the caller's wire contract.
-/
@[pf_entry]
def record (_s : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := invokeSigned 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.selfEntry 15 "log", .u16le value, .u64le value]
    "log" (findPda "log")
  .ok ({ value }, value)

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Svm.SelfLog