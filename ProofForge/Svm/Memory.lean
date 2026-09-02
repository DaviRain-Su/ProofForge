import ProofForge.Core.Ops
import ProofForge.Attr
import ProofForge.Svm.AccountStorage

/-!
# Bounded SVM program-memory contracts

Target-owned descriptors for Solana's `sol_memcpy_`, `sol_memmove_`, `sol_memcmp_`, and
`sol_memset_` host functions. Source programs name checked account-data spans; they never observe
or persist a VM pointer. Invocation-time emission validates account length and destination
authorization before forming transient pointers and issuing one official syscall.
-/

namespace ProofForge.Svm.Memory

/-- Solana's current maximum account data length. Static span geometry cannot exceed this bound. -/
def maxAccountDataBytes : Nat := 10 * 1024 * 1024

/-- One fixed byte interval in a physical transaction account. `endOffset` is exclusive. -/
structure Span where
  account : Nat
  offsetBytes : Nat
  lengthBytes : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Span.account Span.offsetBytes Span.lengthBytes

def Span.endOffset (span : Span) : Nat :=
  span.offsetBytes + span.lengthBytes

def Span.wellFormed (span : Span) (accountLimit : Nat := 64) : Bool :=
  span.account < accountLimit && span.lengthBytes > 0 &&
    span.endOffset ≤ maxAccountDataBytes

def Span.overlaps (left right : Span) : Bool :=
  left.account == right.account &&
    left.offsetBytes < right.endOffset && right.offsetBytes < left.endOffset

/-! ### sf-014：Span 几何 -/

theorem Span.wellFormed_account_lt
    (span : Span) (accountLimit : Nat) (h : span.wellFormed accountLimit = true) :
    span.account < accountLimit := by
  simp [Span.wellFormed] at h
  exact h.1.1

theorem Span.wellFormed_length_pos
    (span : Span) (accountLimit : Nat) (h : span.wellFormed accountLimit = true) :
    0 < span.lengthBytes := by
  simp [Span.wellFormed] at h
  exact h.1.2

theorem Span.wellFormed_endOffset_le
    (span : Span) (accountLimit : Nat) (h : span.wellFormed accountLimit = true) :
    span.endOffset ≤ maxAccountDataBytes := by
  simp [Span.wellFormed] at h
  exact h.2

theorem Span.overlaps_symm (left right : Span) :
    left.overlaps right = right.overlaps left := by
  by_cases ha : left.account = right.account
  · -- same account: overlap is symmetric in the two offset tests
    have hb : (left.account == right.account) = true := by simp [ha]
    have hc : (right.account == left.account) = true := by simp [ha]
    simp only [Span.overlaps, hb, hc, true_and]
    exact Bool.and_comm
      (decide (left.offsetBytes < right.endOffset))
      (decide (right.offsetBytes < left.endOffset))
  · -- distinct accounts: both sides false
    have hb : (left.account == right.account) = false := by
      simp [beq_eq_false_iff_ne, ha]
    have hc : (right.account == left.account) = false := by
      simp [beq_eq_false_iff_ne, Ne.symm ha]
    simp [Span.overlaps, hb, hc]

/-- Same-account spans that abut (`end = start`) do not overlap. -/
theorem Span.abut_not_overlaps (account start mid finish : Nat)
    (hle : start ≤ mid) (hle' : mid ≤ finish) :
    ({ account, offsetBytes := start, lengthBytes := mid - start } : Span).overlaps
        { account, offsetBytes := mid, lengthBytes := finish - mid } = false := by
  simp [Span.overlaps, Span.endOffset]
  intro _
  omega

private def Span.canonical (span : Span) : String :=
  s!"{span.account}.{span.offsetBytes}.{span.lengthBytes}"

private def spanEffects (span : Span) (write : Bool := false) :
    AccountStorage.EffectSummary :=
  { reads := #[span.account]
    writes := if write then #[span.account] else #[] }

/-- Value-producing memory operations. The compare result is the exact signed `i32` syscall
result represented by its zero-extended 32-bit bit pattern in `UInt64`. Equality is still `0`;
signed source arithmetic remains a separate language feature. -/
inductive Query where
  | compare (left right : Span)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat := fun _ => 0

def Query.effects : Query → AccountStorage.EffectSummary
  | .compare left right => (spanEffects left).merge (spanEffects right)

def Query.wellFormed (accountLimit : Nat := 64) : Query → Bool
  | .compare left right =>
      left.wellFormed accountLimit && right.wellFormed accountLimit &&
        left.lengthBytes == right.lengthBytes

def Query.needsWalk : Query → Bool
  | .compare left right => left.account > 0 || right.account > 0

def Query.minAccounts (measure : V → Nat) (operands : Array V) (query : Query) : Nat :=
  let fromSpans := query.effects.reads.foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  operands.foldl (init := fromSpans) fun current value => Nat.max current (measure value)

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .compare left right =>
      let suffix :=
        if operands.isEmpty then ""
        else s!"({String.intercalate "," (operands.map renderValue).toList})"
      s!"mem.cmp.{left.canonical}.{right.canonical}{suffix}"

/-- Effectful official memory operations. `copyNonoverlapping` deliberately rejects overlap;
`move` deliberately permits it. Every destination is checked writable and current-program-owned
by the target backend. -/
inductive Call (V : Type) where
  | copyNonoverlapping (destination source : Span)
  | move (destination source : Span)
  | set (destination : Span) (byte : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .copyNonoverlapping destination source => .copyNonoverlapping destination source
  | .move destination source => .move destination source
  | .set destination byte => .set destination (mapValue byte)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .copyNonoverlapping destination source => return .copyNonoverlapping destination source
  | .move destination source => return .move destination source
  | .set destination byte => return .set destination (← mapValue byte)

def Call.values : Call V → Array V
  | .copyNonoverlapping .. | .move .. => #[]
  | .set _ byte => #[byte]

def Call.effects : Call V → AccountStorage.EffectSummary
  | .copyNonoverlapping destination source | .move destination source =>
      (spanEffects destination true).merge (spanEffects source)
  | .set destination _ => spanEffects destination true

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  let effects := call.effects
  let accounts := (effects.reads ++ effects.writes).foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  call.values.foldl (init := accounts) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .copyNonoverlapping destination source =>
      destination.wellFormed accountLimit && source.wellFormed accountLimit &&
        destination.lengthBytes == source.lengthBytes && !destination.overlaps source
  | .move destination source =>
      destination.wellFormed accountLimit && source.wellFormed accountLimit &&
        destination.lengthBytes == source.lengthBytes
  | .set destination byte => destination.wellFormed accountLimit && valueWellFormed byte

def Call.canonical (renderValue : V → String) : Call V → String
  | .copyNonoverlapping destination source =>
      s!"mem.cpy.{destination.canonical}.{source.canonical}"
  | .move destination source => s!"mem.mov.{destination.canonical}.{source.canonical}"
  | .set destination byte => s!"mem.set.{destination.canonical}({renderValue byte})"

end ProofForge.Svm.Memory
