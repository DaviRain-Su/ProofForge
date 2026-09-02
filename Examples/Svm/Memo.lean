import ProofForge

namespace Examples.Svm.Memo
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- CPI 进 Memo；`"ok"` 是本应用选择的静态 payload。 -/
@[pf_entry]
def write (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Svm.Sdk.Memo.Ascii.write "ok"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Svm.Memo