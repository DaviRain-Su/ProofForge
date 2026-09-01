import ProofForge.Svm.Sdk.Transient
import ProofForge.Svm.Sdk.TransientVec
import ProofForge.Svm.TransientVec

/-!
# Transient Vector64 model (sf-006)

Invocation-local two-slot abstract store for `Sdk.Transient.Vector64`. Captures the Emit
lifecycle (active + capacity match, bounds/full, finish invalidate) without modeling the real
bump allocator address space.
-/

namespace ProofForge.Svm.Sdk.TransientModel

open ProofForge.Svm.Sdk.Transient
open ProofForge.Svm.TransientVec

/-! ## Error vocabulary (align `TransientVec`) -/

def oomCode : UInt64 := UInt64.ofNat oomErrorCode
def boundsCode : UInt64 := UInt64.ofNat boundsErrorCode
def stateCode : UInt64 := UInt64.ofNat stateErrorCode
def okCode : UInt64 := 0

/-! ## Abstract store -/

private def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun x => if x = a then v else f x

private theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) :
    upd f a v a = v := by
  simp [upd]

private theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a a' : α}
    (hne : a' ≠ a) (v : β) : upd f a v a' = f a' := by
  simp [upd, hne]

/-- Per-slot metadata bank (active / capacity / length). -/
structure SlotBank where
  active : Bool := false
  capacity : Nat := 0
  length : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Two independent handle slots plus per-slot payload words. -/
structure TransientWords where
  bank : Fin 2 → SlotBank
  words : Fin 2 → Nat → UInt64

def empty : TransientWords :=
  { bank := fun _ => {}, words := fun _ _ => 0 }

def slotOf (word : Nat) : Option (Fin 2) :=
  let s := handleSlot word
  if h : s < 2 then some ⟨s, h⟩ else none

def payloadOf (word : Nat) : Nat := handlePayload word

def setBank (tw : TransientWords) (slot : Fin 2) (b : SlotBank) : TransientWords :=
  { tw with bank := upd tw.bank slot b }

def setWord (tw : TransientWords) (slot : Fin 2) (i : Nat) (v : UInt64) : TransientWords :=
  { tw with words := upd tw.words slot (upd (tw.words slot) i v) }

def requireActive (tw : TransientWords) (slot : Fin 2) (cap : Nat) : Bool :=
  let b := tw.bank slot
  b.active && decide (b.capacity = cap)

/-! ## Vector64 operations -/

def mVec64Begin (tw : TransientWords) (slot : Fin 2) (cap : Nat) : TransientWords × UInt64 :=
  if cap = 0 then (tw, stateCode)
  else
    (setBank tw slot { active := true, capacity := cap, length := 0 }, okCode)

def mVec64Push (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64) :
    TransientWords × UInt64 :=
  if !requireActive tw slot cap then (tw, stateCode)
  else
    let b := tw.bank slot
    if b.length ≥ cap then (tw, boundsCode)
    else
      let tw := setWord tw slot b.length value
      (setBank tw slot { b with length := b.length + 1 }, okCode)

def mVec64Set (tw : TransientWords) (slot : Fin 2) (cap : Nat) (index : Nat) (value : UInt64) :
    TransientWords × UInt64 :=
  if !requireActive tw slot cap then (tw, stateCode)
  else
    let b := tw.bank slot
    if index ≥ b.length then (tw, boundsCode)
    else
      (setWord tw slot index value, okCode)

def mVec64Pop (tw : TransientWords) (slot : Fin 2) (cap : Nat) :
    TransientWords × UInt64 :=
  if !requireActive tw slot cap then (tw, stateCode)
  else
    let b := tw.bank slot
    if b.length = 0 then (tw, boundsCode)
    else
      let i := b.length - 1
      let v := tw.words slot i
      (setBank tw slot { b with length := i }, v)

def mVec64Get (tw : TransientWords) (slot : Fin 2) (cap : Nat) (index : Nat) : UInt64 :=
  if !requireActive tw slot cap then stateCode
  else
    let b := tw.bank slot
    if index ≥ b.length then boundsCode
    else tw.words slot index

def mVec64Length (tw : TransientWords) (slot : Fin 2) (cap : Nat) : UInt64 :=
  if !requireActive tw slot cap then stateCode
  else UInt64.ofNat (tw.bank slot).length

def mVec64Finish (tw : TransientWords) (slot : Fin 2) (cap : Nat) :
    TransientWords × UInt64 :=
  if !requireActive tw slot cap then (tw, stateCode)
  else
    (setBank tw slot {}, okCode)

/-! ## Fail-closed -/

theorem mVec64Push_stale (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64)
    (h : requireActive tw slot cap = false) :
    mVec64Push tw slot cap value = (tw, stateCode) := by
  simp [mVec64Push, h]

theorem mVec64Push_full (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hfull : (tw.bank slot).length ≥ cap) :
    mVec64Push tw slot cap value = (tw, boundsCode) := by
  simp [mVec64Push, hact, hfull]

theorem mVec64Set_oob (tw : TransientWords) (slot : Fin 2) (cap : Nat) (index : Nat)
    (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hoob : index ≥ (tw.bank slot).length) :
    mVec64Set tw slot cap index value = (tw, boundsCode) := by
  simp [mVec64Set, hact, hoob]

theorem mVec64Pop_empty (tw : TransientWords) (slot : Fin 2) (cap : Nat)
    (hact : requireActive tw slot cap = true)
    (hempty : (tw.bank slot).length = 0) :
    mVec64Pop tw slot cap = (tw, boundsCode) := by
  simp [mVec64Pop, hact, hempty]

theorem mVec64Finish_stale (tw : TransientWords) (slot : Fin 2) (cap : Nat)
    (h : requireActive tw slot cap = false) :
    mVec64Finish tw slot cap = (tw, stateCode) := by
  simp [mVec64Finish, h]

/-! ## Push readback + slot isolation -/

private theorem mVec64Push_eq (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hroom : (tw.bank slot).length < cap) :
    mVec64Push tw slot cap value =
      (setBank (setWord tw slot (tw.bank slot).length value)
        slot { tw.bank slot with length := (tw.bank slot).length + 1 }, okCode) := by
  have hge : ¬((tw.bank slot).length ≥ cap) := Nat.not_le_of_gt hroom
  simp [mVec64Push, hact, hge]

/-- Push succeeds and stores `value` at the old length; length advances by one. -/
theorem mVec64Push_readback (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hroom : (tw.bank slot).length < cap) :
    let r := mVec64Push tw slot cap value
    r.2 = okCode ∧
    r.1.words slot (tw.bank slot).length = value ∧
    (r.1.bank slot).length = (tw.bank slot).length + 1 ∧
    requireActive r.1 slot cap = true := by
  have hr := mVec64Push_eq tw slot cap value hact hroom
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hr]
  · simp [hr, setBank, setWord, upd_same]
  · simp [hr, setBank, upd_same]
  · have := hact
    simp [requireActive] at this ⊢
    simp [hr, setBank, setWord, upd_same, this]

/-- After a successful push, `mVec64Get` returns the stored value. -/
theorem mVec64Push_get (tw : TransientWords) (slot : Fin 2) (cap : Nat) (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hroom : (tw.bank slot).length < cap) :
    mVec64Get (mVec64Push tw slot cap value).1 slot cap (tw.bank slot).length = value := by
  have hr := mVec64Push_readback tw slot cap value hact hroom
  have hact' : requireActive (mVec64Push tw slot cap value).1 slot cap = true := hr.2.2.2
  have hlen :
      ¬((tw.bank slot).length ≥ ((mVec64Push tw slot cap value).1.bank slot).length) := by
    have := hr.2.2.1
    omega
  simp [mVec64Get, hact', hlen, hr.2.1]

theorem mVec64Push_other_slot_unchanged (tw : TransientWords) (slot other : Fin 2)
    (cap : Nat) (value : UInt64)
    (hact : requireActive tw slot cap = true)
    (hroom : (tw.bank slot).length < cap)
    (hne : slot ≠ other) :
    let r := mVec64Push tw slot cap value
    r.1.bank other = tw.bank other ∧
    (∀ i, r.1.words other i = tw.words other i) := by
  have hr := mVec64Push_eq tw slot cap value hact hroom
  constructor
  · simp [hr, setBank, setWord, upd_ne (a := slot) (a' := other) tw.bank hne.symm]
  · intro i
    have hw :=
      upd_ne (β := Nat → UInt64) tw.words (a := slot) (a' := other) hne.symm
        (upd (tw.words slot) (tw.bank slot).length value)
    simpa [hr, setBank, setWord] using congrArg (fun f => f i) hw

theorem mVec64Begin_finish_stale (tw : TransientWords) (slot : Fin 2) (cap : Nat)
    (hcap : cap ≠ 0) :
    let mid := (mVec64Begin tw slot cap).1
    let done := (mVec64Finish mid slot cap).1
    requireActive done slot cap = false := by
  simp [mVec64Begin, hcap, mVec64Finish, setBank, requireActive, upd_same]

end ProofForge.Svm.Sdk.TransientModel
