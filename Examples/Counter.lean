import SolanaLean

namespace Examples.Counter

open SolanaLean.Counter
open SolanaLean.IR

/-!
  合约就是普通 Lean。没有 `program … where`。
  证明也钉在这些函数上，不钉 DSL AST。
-/

def program : Program := counterProgram

example : isCounterShape program := by native_decide

theorem overflow_not_ok
    (s : State) (d : UInt64)
    (h : increment s d = .error .overflow) :
    ¬ ∃ t r, increment s d = .ok (t, r) :=
  increment_overflow_not_ok s d h

end Examples.Counter
