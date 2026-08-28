import ProofForge

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
@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

/-- checked add：溢出则失败，不更新状态。 -/
@[pf_entry]
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
@[pf_entry]
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
@[pf_entry]
def scale (s : State) (factor : UInt64) : Except Error (State × UInt64) :=
  if factor = 0 then
    .ok ({ value := 0 }, 0)
  else if s.value ≤ u64Max / factor then
    let next := s.value * factor
    .ok ({ value := next }, next)
  else
    .error .overflow

@[pf_entry]
def divide (s : State) (den : UInt64) : Except Error (State × UInt64) :=
  if den ≠ 0 then
    let next := s.value / den
    .ok ({ value := next }, next)
  else
    .error .overflow

@[pf_entry]
def modulo (s : State) (den : UInt64) : Except Error (State × UInt64) :=
  if den ≠ 0 then
    let next := s.value % den
    .ok ({ value := next }, next)
  else
    .error .overflow

/-- view：value = 0 返回 1，否则 0。 -/ 
@[pf_entry]
def nonzero (s : State) : UInt64 :=
  if s.value = 0 then 1 else 0

section Proofs

/-! ## 第一批 kernel 证明：Counter 后置条件与不变量

这些定理是对上面 `@[pf_entry]` 合约函数的普通 kernel-checked 性质，与编译走同一个
digest（见 README 信任边界）：证的主语就是编的主语。 -/

/-- 成功路径后置条件：新值恰为 `s.value + d`，且返回值等于新状态值。 -/ 
theorem increment_ok (s : State) (d : UInt64) {t : State} {r : UInt64}
    (h : increment s d = .ok (t, r)) :
    t.value = s.value + d ∧ r = t.value := by
  unfold increment at h
  split at h
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp at h

/-- 单调性：成功路径下值不减（guard 保证不回绕）。 -/ 
theorem increment_ok_bound (s : State) (d : UInt64) {t : State} {r : UInt64}
    (h : increment s d = .ok (t, r)) : s.value ≤ t.value := by
  have hv := increment_ok s d h
  show s.value.toNat ≤ t.value.toNat
  rw [hv.1, UInt64.toNat_add]
  have hst : s.value.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size s.value
  have hdt : d.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size d
  have hmax : u64Max.toNat = 18446744073709551615 := by rfl
  -- guard：s.value ≤ u64Max - d
  have hsub : (u64Max - d).toNat = 18446744073709551615 - d.toNat := by
    simp only [UInt64.toNat_sub]
    have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
    rw [h2, hmax]
    omega
  -- 从 h 反解 guard（失败分支已排除）
  unfold increment at h
  split at h
  · rename_i hc
    have hc' : s.value.toNat ≤ (u64Max - d).toNat := hc
    rw [hsub] at hc'
    have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
    omega
  · simp at h

/-- 成功路径后置条件：新值恰为 `s.value - d`，且返回值等于新状态值。 -/ 
theorem decrement_ok (s : State) (d : UInt64) {t : State} {r : UInt64}
    (h : decrement s d = .ok (t, r)) :
    t.value = s.value - d ∧ r = t.value := by
  unfold decrement at h
  split at h
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp at h

/-- 单调性：成功路径下值不增。 -/ 
theorem decrement_ok_le (s : State) (d : UInt64) {t : State} {r : UInt64}
    (h : decrement s d = .ok (t, r)) : t.value ≤ s.value := by
  have hv := decrement_ok s d h
  show t.value.toNat ≤ s.value.toNat
  unfold decrement at h
  split at h
  · rename_i hc
    have hc' : d.toNat ≤ s.value.toNat := hc
    rw [hv.1, UInt64.toNat_sub s.value d]
    have hst : s.value.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size s.value
    have hdt : d.toNat < 4294967296 * 4294967296 := UInt64.toNat_lt_size d
    have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    omega
  · simp at h

/-- `factor = 0` 时 scale 归零。 -/ 
theorem scale_zero (s : State) :
    scale s 0 = .ok ({ value := 0 }, 0) := by
  simp [scale]

/-- 成功路径后置条件（`factor ≠ 0`）：新值恰为 `s.value * factor`。 -/ 
theorem scale_ok (s : State) (f : UInt64) {t : State} {r : UInt64}
    (hne : f ≠ 0) (h : scale s f = .ok (t, r)) :
    t.value = s.value * f ∧ r = t.value := by
  unfold scale at h
  split at h
  · rename_i hz
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by subst hz; simp, rfl⟩
  · split at h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp at h

/-- `den = 0` 时 divide 必失败，不更新状态。 -/ 
theorem divide_zero_error (s : State) :
    divide s 0 = .error .overflow := by
  simp [divide]

/-- `den = 0` 时 modulo 必失败，不更新状态。 -/ 
theorem modulo_zero_error (s : State) :
    modulo s 0 = .error .overflow := by
  simp [modulo]

end Proofs

end Examples.Counter
