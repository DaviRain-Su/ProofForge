import ProofForge.Svm.Sdk.Transient
import ProofForge.Svm.Sdk.TransientVec
import ProofForge.Svm.TransientVec
import ProofForge.Svm.TransientBytes

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

/-! ## Bytes store (sf-007)

Two byte slots, independent of Vector64 banks. Byte values must be `≤ 255`; `appendLe64`
requires eight free bytes and writes little-endian limbs without a partial prefix on failure. -/

def bytesOomCode : UInt64 := UInt64.ofNat ProofForge.Svm.TransientBytes.oomErrorCode
def bytesBoundsCode : UInt64 := UInt64.ofNat ProofForge.Svm.TransientBytes.boundsErrorCode
def bytesStateCode : UInt64 := UInt64.ofNat ProofForge.Svm.TransientBytes.stateErrorCode
def bytesRangeCode : UInt64 := UInt64.ofNat ProofForge.Svm.TransientBytes.rangeErrorCode

structure BytesBank where
  active : Bool := false
  capacity : Nat := 0
  length : Nat := 0
  deriving BEq, Repr, Inhabited

structure BytesWords where
  bank : Fin 2 → BytesBank
  bytes : Fin 2 → Nat → UInt8

def emptyBytes : BytesWords :=
  { bank := fun _ => {}, bytes := fun _ _ => 0 }

def setBytesBank (bw : BytesWords) (slot : Fin 2) (b : BytesBank) : BytesWords :=
  { bw with bank := upd bw.bank slot b }

def setByte (bw : BytesWords) (slot : Fin 2) (i : Nat) (v : UInt8) : BytesWords :=
  { bw with bytes := upd bw.bytes slot (upd (bw.bytes slot) i v) }

def requireBytesActive (bw : BytesWords) (slot : Fin 2) (cap : Nat) : Bool :=
  let b := bw.bank slot
  b.active && decide (b.capacity = cap)

def mBytesBegin (bw : BytesWords) (slot : Fin 2) (cap : Nat) : BytesWords × UInt64 :=
  if cap = 0 then (bw, bytesStateCode)
  else
    (setBytesBank bw slot { active := true, capacity := cap, length := 0 }, okCode)

def mBytesPush (bw : BytesWords) (slot : Fin 2) (cap : Nat) (byte : UInt64) :
    BytesWords × UInt64 :=
  if !requireBytesActive bw slot cap then (bw, bytesStateCode)
  else if byte > 255 then (bw, bytesRangeCode)
  else
    let b := bw.bank slot
    if b.length ≥ cap then (bw, bytesBoundsCode)
    else
      let bw := setByte bw slot b.length (UInt8.ofNat byte.toNat)
      (setBytesBank bw slot { b with length := b.length + 1 }, okCode)

/-- Append eight LE bytes, or leave the store unchanged when room/range/state fails. -/
def mBytesAppendLe64 (bw : BytesWords) (slot : Fin 2) (cap : Nat) (value : UInt64) :
    BytesWords × UInt64 :=
  if !requireBytesActive bw slot cap then (bw, bytesStateCode)
  else
    let b := bw.bank slot
    if b.length + 8 > cap then (bw, bytesBoundsCode)
    else
      let write (bw : BytesWords) (off : Nat) (byte : UInt8) : BytesWords :=
        setByte bw slot (b.length + off) byte
      let bw := write bw 0 (UInt8.ofNat (value.toNat % 256))
      let bw := write bw 1 (UInt8.ofNat ((value.toNat / 256) % 256))
      let bw := write bw 2 (UInt8.ofNat ((value.toNat / 256 ^ 2) % 256))
      let bw := write bw 3 (UInt8.ofNat ((value.toNat / 256 ^ 3) % 256))
      let bw := write bw 4 (UInt8.ofNat ((value.toNat / 256 ^ 4) % 256))
      let bw := write bw 5 (UInt8.ofNat ((value.toNat / 256 ^ 5) % 256))
      let bw := write bw 6 (UInt8.ofNat ((value.toNat / 256 ^ 6) % 256))
      let bw := write bw 7 (UInt8.ofNat ((value.toNat / 256 ^ 7) % 256))
      (setBytesBank bw slot { b with length := b.length + 8 }, okCode)

theorem mBytesPush_range (bw : BytesWords) (slot : Fin 2) (cap : Nat) (byte : UInt64)
    (hact : requireBytesActive bw slot cap = true) (hoob : byte > 255) :
    mBytesPush bw slot cap byte = (bw, bytesRangeCode) := by
  simp [mBytesPush, hact, hoob]

theorem mBytesAppendLe64_no_room (bw : BytesWords) (slot : Fin 2) (cap : Nat)
    (value : UInt64)
    (hact : requireBytesActive bw slot cap = true)
    (hfull : (bw.bank slot).length + 8 > cap) :
    mBytesAppendLe64 bw slot cap value = (bw, bytesBoundsCode) := by
  simp [mBytesAppendLe64, hact, hfull]

theorem mBytesAppendLe64_stale (bw : BytesWords) (slot : Fin 2) (cap : Nat)
    (value : UInt64) (h : requireBytesActive bw slot cap = false) :
    mBytesAppendLe64 bw slot cap value = (bw, bytesStateCode) := by
  simp [mBytesAppendLe64, h]

/-! ## Combined invocation scratch: vec slots ⟂ bytes slots -/

structure InvocationScratch where
  vec : TransientWords := empty
  bytes : BytesWords := emptyBytes

/-- Updating the vec component leaves the bytes component identical. -/
theorem invocation_vec_update_preserves_bytes (s : InvocationScratch)
    (vec' : TransientWords) :
    ({ s with vec := vec' } : InvocationScratch).bytes = s.bytes :=
  rfl

/-- Updating the bytes component leaves the vec component identical. -/
theorem invocation_bytes_update_preserves_vec (s : InvocationScratch)
    (bytes' : BytesWords) :
    ({ s with bytes := bytes' } : InvocationScratch).vec = s.vec :=
  rfl

/-- A successful vec push composed into the scratch keeps the original bytes banks. -/
theorem mVec64Push_scratch_preserves_bytes (s : InvocationScratch) (slot : Fin 2)
    (cap : Nat) (value : UInt64)
    (_hact : requireActive s.vec slot cap = true)
    (_hroom : (s.vec.bank slot).length < cap) :
    let s' : InvocationScratch := { s with vec := (mVec64Push s.vec slot cap value).1 }
    s'.bytes = s.bytes := by
  rfl

/-- A successful bytes push composed into the scratch keeps the original vec banks. -/
theorem mBytesPush_scratch_preserves_vec (s : InvocationScratch) (slot : Fin 2)
    (cap : Nat) (byte : UInt64)
    (_hact : requireBytesActive s.bytes slot cap = true)
    (_hin : byte ≤ 255)
    (_hroom : (s.bytes.bank slot).length < cap) :
    let s' : InvocationScratch := { s with bytes := (mBytesPush s.bytes slot cap byte).1 }
    s'.vec = s.vec := by
  rfl

/-! ## Record64 / WideVec whole-record preflight (sf-007)

Modeled over Vector64 length: an append of `limbs` words is rejected before any write when
`length + limbs > capacity`, so no partial record prefix is left. -/

def recordHasRoom (length capacity limbs : Nat) : Bool :=
  decide (length + limbs ≤ capacity)

/-- A 1-limb record append with no room is exactly a full Vector64 push (store unchanged). -/
theorem mRecordAppend1_rejected_noop (tw : TransientWords) (slot : Fin 2)
    (cap : Nat) (v0 : UInt64)
    (hact : requireActive tw slot cap = true)
    (hno : recordHasRoom (tw.bank slot).length cap 1 = false) :
    mVec64Push tw slot cap v0 = (tw, boundsCode) := by
  have : (tw.bank slot).length ≥ cap := by
    simp [recordHasRoom] at hno
    omega
  exact mVec64Push_full tw slot cap v0 hact this

/-- Without room for two limbs, the first word push of a Vector128 is rejected (no partial). -/
theorem mVec128Push_first_rejected (tw : TransientWords) (slot : Fin 2) (cap : Nat)
    (w0 : UInt64)
    (hact : requireActive tw slot cap = true)
    (_hno : recordHasRoom (tw.bank slot).length cap 2 = false)
    (hfull : (tw.bank slot).length ≥ cap) :
    mVec64Push tw slot cap w0 = (tw, boundsCode) :=
  mVec64Push_full tw slot cap w0 hact hfull

end ProofForge.Svm.Sdk.TransientModel
