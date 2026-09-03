import ProofForge.Attr

/-!
# Shared TokenShape (N15 / wsm-near-conformance-001)

Minimal **transfer-shaped** UInt64 ledger shared by SVM, EVM, and NEAR — the conceptual
subset that all three targets can lower from one Lean source (mirroring `Examples.Counter`).

This is **not** ERC-20 / SPL / NEP-141 wire: no `approve` / allowance (NEAR NEP-141 has none;
SVM+EVM approve fixtures stay target-local). Digests differ by target and are pinned in
`Tests/CrossTargetTokenShapeSpec`.
-/

namespace Examples.TokenShape

structure State where
  balance : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (initial : UInt64) : State :=
  { balance := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.balance

/-- Credit `amount` into the single balance (checked add). -/
@[pf_entry]
def credit (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if s.balance ≤ u64Max - amount then
    let next := s.balance + amount
    .ok ({ balance := next }, next)
  else
    .error .overflow

/-- Debit `amount` from the single balance (checked sub). Transfer-shaped mutual of `credit`. -/
@[pf_entry]
def debit (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if amount ≤ s.balance then
    let next := s.balance - amount
    .ok ({ balance := next }, next)
  else
    .error .overflow

theorem credit_overflow_not_ok
    (s : State) (a : UInt64)
    (h : credit s a = .error .overflow) :
    ¬ ∃ t r, credit s a = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

theorem debit_underflow_not_ok
    (s : State) (a : UInt64)
    (h : debit s a = .error .overflow) :
    ¬ ∃ t r, debit s a = .ok (t, r) := by
  intro ⟨t, r, hok⟩
  have : Except.error Error.overflow = Except.ok (t, r) := h.symm.trans hok
  cases this

end Examples.TokenShape
