import ProofForge

namespace Examples.Svm.Keccak
open ProofForge.Svm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 无参 mutate 占入口。 -/
@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

/-- `keccak256("vault")` 的第一个小端 u64。 -/
@[pf_entry]
def vault (_s : State) : UInt64 :=
  keccak256Lit "vault"

/-- `keccak256("ok")` 的第一个小端 u64。 -/
@[pf_entry]
def ok (_s : State) : UInt64 :=
  keccak256Lit "ok"

/-- `keccak256("")` 的第一个小端 u64。 -/
@[pf_entry]
def empty (_s : State) : UInt64 :=
  keccak256Lit ""

end Examples.Svm.Keccak