import SolanaLean

namespace Examples.Counter

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- 2^64 - 1。Lean 4.31 无 `UInt64.max`。 -/
def u64Max : UInt64 := ~~~(0 : UInt64)

/-- 不用 `initialize`：那是 Lean 的命令关键字。 -/
@[solana_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[solana_entry]
def get (s : State) : UInt64 :=
  s.value

/-- checked add：溢出则失败，不更新状态。 -/
@[solana_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

theorem increment_overflow_not_ok
    (s : State) (d : UInt64)
    (h : increment s d = .error .overflow) :
    ¬ ∃ t r, increment s d = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

/-- `delta ≤ s.value` 才减，否则 overflow。 -/
@[solana_entry]
def decrement (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if delta ≤ s.value then
    let next := s.value - delta
    .ok ({ value := next }, next)
  else
    .error .overflow

theorem decrement_underflow_not_ok
    (s : State) (d : UInt64)
    (h : decrement s d = .error .overflow) :
    ¬ ∃ t r, decrement s d = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

/-- `factor = 0` 得 0；否则 `value ≤ u64Max / factor` 才乘。 -/
@[solana_entry]
def scale (s : State) (factor : UInt64) : Except Error (State × UInt64) :=
  if factor = 0 then
    .ok ({ value := 0 }, 0)
  else if s.value ≤ u64Max / factor then
    let next := s.value * factor
    .ok ({ value := next }, next)
  else
    .error .overflow

@[solana_entry]
def divide (s : State) (den : UInt64) : Except Error (State × UInt64) :=
  if den ≠ 0 then
    let next := s.value / den
    .ok ({ value := next }, next)
  else
    .error .overflow

@[solana_entry]
def modulo (s : State) (den : UInt64) : Except Error (State × UInt64) :=
  if den ≠ 0 then
    let next := s.value % den
    .ok ({ value := next }, next)
  else
    .error .overflow

/-- view：value = 0 返回 1，否则 0。 -/
@[solana_entry]
def nonzero (s : State) : UInt64 :=
  if s.value = 0 then 1 else 0

end Examples.Counter
