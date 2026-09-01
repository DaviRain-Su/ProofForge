import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.Storage

/-!
# Allocator model (sf-008)

AccountWords model of `Allocator` (`OneBasedAllocator`): one-based indices,
packed `cursor = bump ||| (freeHead <<< 32)`, free-list before bump.

## SF-5a knives (task `sf-008`)

* `mAlloc_full_zero` — `capacity ≤ liveCount` → `0`, memory unchanged.
* `mAlloc_free_alloc_same` — bump → free → alloc returns the same index.
-/

namespace ProofForge.Svm.Sdk.AllocatorModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageModel

/-- Cursor packing used by `Allocator.alloc` / `free`. -/
@[inline] def packCursor (bump freeHead : UInt64) : UInt64 :=
  bump ||| (freeHead <<< 32)

@[inline] def unpackBump (cursor : UInt64) : UInt64 :=
  cursor &&& 0xffffffff

@[inline] def unpackFreeHead (cursor : UInt64) : UInt64 :=
  cursor >>> 32

theorem pack_1_0 : packCursor 1 0 = 1 := by native_decide
theorem pack_2_0 : packCursor 2 0 = 2 := by native_decide
theorem pack_2_2 : packCursor 2 2 = (2 : UInt64) ||| ((2 : UInt64) <<< 32) := by rfl
theorem unpack_initialCursor :
    unpackBump Allocator.initialCursor = 1 ∧
      unpackFreeHead Allocator.initialCursor = 1 := by
  native_decide

private theorem u64_toNat_0 : (0 : UInt64).toNat = 0 := rfl
private theorem u64_toNat_1 : (1 : UInt64).toNat = 1 := rfl
private theorem u64_toNat_2 : (2 : UInt64).toNat = 2 := rfl

/-- Slot links field: word 0 of each one-based slot (SDK `{ region := slots }`). -/
@[inline] def slotsField (a : Allocator) : Field :=
  { region := a.slots }

@[inline] def liveField (a : Allocator) : Field :=
  OneBasedAllocator.liveCount a

@[inline] def mLiveCount (mem : AccountWords) (a : Allocator) : UInt64 :=
  mReadField mem (liveField a) 0

@[inline] def mCursor (mem : AccountWords) (a : Allocator) : UInt64 :=
  mReadField mem a.cursor 0

@[inline] def mSlotWord (mem : AccountWords) (a : Allocator) (slot : UInt64) : UInt64 :=
  mReadField mem (slotsField a) slot

/-- Model of `Allocator.initialize`. -/
def mAllocInitialize (mem : AccountWords) (a : Allocator) : AccountWords × UInt64 :=
  let mem := mWriteField mem (liveField a) 0 0
  let mem := mWriteField mem a.cursor 0 Allocator.initialCursor
  (mem, 1)

/-- Model of `Allocator.alloc` (returns `(memory, index)`).

Guards are inlined so `if_neg` / `if_pos` match the surface `if`s. -/
def mAlloc (mem : AccountWords) (a : Allocator) : AccountWords × UInt64 :=
  if UInt64.ofNat a.slots.capacity ≤ mLiveCount mem a then
    (mem, 0)
  else if unpackFreeHead (mCursor mem a) ≠ 0 then
    let freeHead := unpackFreeHead (mCursor mem a)
    let bump := unpackBump (mCursor mem a)
    let count := mLiveCount mem a
    let next := mSlotWord mem a freeHead
    let mem := mWriteField mem a.cursor 0 (packCursor bump next)
    let mem := mWriteField mem (liveField a) 0 (count + 1)
    (mem, freeHead)
  else if unpackBump (mCursor mem a) < UInt64.ofNat a.slots.capacity then
    let bump := unpackBump (mCursor mem a)
    let count := mLiveCount mem a
    let mem := mWriteField mem a.cursor 0 (packCursor (bump + 1) 0)
    let mem := mWriteField mem (liveField a) 0 (count + 1)
    (mem, bump + 1)
  else
    (mem, 0)

/-- Model of `Allocator.free` (returns `(memory, slotOrZero)`). -/
def mFree (mem : AccountWords) (a : Allocator) (slot : UInt64) : AccountWords × UInt64 :=
  if slot = 0
      || unpackBump (mCursor mem a) < slot
      || UInt64.ofNat a.slots.capacity < slot
      || mLiveCount mem a = 0 then
    (mem, 0)
  else
    let bump := unpackBump (mCursor mem a)
    let freeHead := unpackFreeHead (mCursor mem a)
    let count := mLiveCount mem a
    let mem := mWriteField mem (slotsField a) slot freeHead
    let mem := mWriteField mem a.cursor 0 (packCursor bump slot)
    let mem := mWriteField mem (liveField a) 0 (count - 1)
    (mem, slot)

/-! ## Exhaustion / null free -/

theorem mAlloc_full_zero
    (mem : AccountWords) (a : Allocator)
    (hfull : UInt64.ofNat a.slots.capacity ≤ mLiveCount mem a) :
    mAlloc mem a = (mem, 0) := by
  simp [mAlloc, hfull]

theorem mFree_null_zero (mem : AccountWords) (a : Allocator) :
    mFree mem a 0 = (mem, 0) := by
  simp [mFree]

theorem mFree_empty_zero
    (mem : AccountWords) (a : Allocator) (slot : UInt64)
    (hne : slot ≠ 0) (hCount : mLiveCount mem a = 0) :
    mFree mem a slot = (mem, 0) := by
  simp [mFree, hne, hCount]

/-! ## Word geometry for the bump→free→alloc narrative -/

/-- Concrete word addresses for live/cursor/slot-2 used by the SF-5a roundtrip. -/
structure AllocWords (a : Allocator) where
  liveW : Nat
  cursorW : Nat
  slot2W : Nat
  hl : mFieldWord (liveField a) 0 = some liveW
  hc : mFieldWord a.cursor 0 = some cursorW
  hs : mFieldWord (slotsField a) 2 = some slot2W
  live_ne_cursor : liveW ≠ cursorW
  live_ne_slot2 : liveW ≠ slot2W
  cursor_ne_slot2 : cursorW ≠ slot2W

private theorem unpack_pack_1_0 :
    unpackBump (packCursor 1 0) = 1 ∧ unpackFreeHead (packCursor 1 0) = 0 := by
  native_decide

private theorem unpack_pack_2_0 :
    unpackBump (packCursor 2 0) = 2 ∧ unpackFreeHead (packCursor 2 0) = 0 := by
  native_decide

private theorem unpack_pack_2_2 :
    unpackBump (packCursor 2 2) = 2 ∧ unpackFreeHead (packCursor 2 2) = 2 := by
  native_decide

private theorem not_cap_le_zero
    {cap : UInt64} (hCap : (2 : UInt64) ≤ cap) :
    ¬ (cap ≤ (0 : UInt64)) := by
  intro h
  have h1 := (UInt64.le_iff_toNat_le).mp h
  have h2 := (UInt64.le_iff_toNat_le).mp hCap
  simp [u64_toNat_2] at h1 h2
  omega

private theorem one_lt_of_two_le
    {cap : UInt64} (hCap : (2 : UInt64) ≤ cap) :
    (1 : UInt64) < cap := by
  have h2 := (UInt64.le_iff_toNat_le).mp hCap
  exact (UInt64.lt_iff_toNat_lt).2 (by simp [u64_toNat_1, u64_toNat_2] at h2 ⊢; omega)

private theorem not_cap_lt_two
    {cap : UInt64} (hCap : (2 : UInt64) ≤ cap) :
    ¬ (cap < (2 : UInt64)) := by
  intro h
  have h1 := (UInt64.lt_iff_toNat_lt).mp h
  have h2 := (UInt64.le_iff_toNat_le).mp hCap
  simp [u64_toNat_2] at h1 h2
  omega

/-- First alloc from empty freelist + `count = 0` + `cursor = pack 1 0` yields index `2`. -/
theorem mAlloc_bump_first
    (mem : AccountWords) (a : Allocator) (w : AllocWords a)
    (hCap : (2 : UInt64) ≤ UInt64.ofNat a.slots.capacity)
    (hCount : mLiveCount mem a = 0)
    (hCursor : mCursor mem a = packCursor 1 0) :
    (mAlloc mem a).2 = 2 ∧
      mLiveCount (mAlloc mem a).1 a = 1 ∧
      mCursor (mAlloc mem a).1 a = packCursor 2 0 := by
  have hBump : unpackBump (mCursor mem a) = 1 := by
    simpa [hCursor] using unpack_pack_1_0.1
  have hFree : unpackFreeHead (mCursor mem a) = 0 := by
    simpa [hCursor] using unpack_pack_1_0.2
  have hFull : ¬ (UInt64.ofNat a.slots.capacity ≤ mLiveCount mem a) := by
    simpa [hCount] using not_cap_le_zero hCap
  have hFreeNe : ¬ (unpackFreeHead (mCursor mem a) ≠ 0) := by
    simp [hFree]
  have hLt : unpackBump (mCursor mem a) < UInt64.ofNat a.slots.capacity := by
    simpa [hBump] using one_lt_of_two_le hCap
  have hAlloc :
      mAlloc mem a =
        (mWriteField
          (mWriteField mem a.cursor 0 (packCursor 2 0))
          (liveField a) 0 1, 2) := by
    unfold mAlloc
    rw [if_neg hFull, if_neg hFreeNe, if_pos hLt]
    simp [hBump, hCount, pack_2_0]
  refine ⟨by simp [hAlloc], ?_, ?_⟩
  · have := mReadField_write_same
      (mWriteField mem a.cursor 0 (packCursor 2 0))
      (liveField a) 0 1 w.liveW w.hl
    simpa [hAlloc, mLiveCount, liveField] using this
  · have hother := mReadField_write_other
      (mWriteField mem a.cursor 0 (packCursor 2 0))
      a.cursor (liveField a) 0 0 1 w.hc w.hl w.live_ne_cursor.symm
    have hsame := mReadField_write_same mem a.cursor 0 (packCursor 2 0) w.cursorW w.hc
    simpa [hAlloc, mCursor] using hother.trans hsame

/-- Free of bump-allocated index `2` under the post-state of `mAlloc_bump_first`. -/
theorem mFree_after_bump_first
    (mem : AccountWords) (a : Allocator) (w : AllocWords a)
    (hCap : (2 : UInt64) ≤ UInt64.ofNat a.slots.capacity)
    (hCount : mLiveCount mem a = 0)
    (hCursor : mCursor mem a = packCursor 1 0) :
    (mFree (mAlloc mem a).1 a 2).2 = 2 ∧
      mLiveCount (mFree (mAlloc mem a).1 a 2).1 a = 0 ∧
      mCursor (mFree (mAlloc mem a).1 a 2).1 a = packCursor 2 2 ∧
      mSlotWord (mFree (mAlloc mem a).1 a 2).1 a 2 = 0 := by
  have hA := mAlloc_bump_first mem a w hCap hCount hCursor
  have hCountA : mLiveCount (mAlloc mem a).1 a = 1 := hA.2.1
  have hCursorA : mCursor (mAlloc mem a).1 a = packCursor 2 0 := hA.2.2
  have hBump : unpackBump (mCursor (mAlloc mem a).1 a) = 2 := by
    simpa [hCursorA] using unpack_pack_2_0.1
  have hFree : unpackFreeHead (mCursor (mAlloc mem a).1 a) = 0 := by
    simpa [hCursorA] using unpack_pack_2_0.2
  have hguard :
      ¬ (((2 : UInt64) = 0)
          || unpackBump (mCursor (mAlloc mem a).1 a) < 2
          || UInt64.ofNat a.slots.capacity < 2
          || mLiveCount (mAlloc mem a).1 a = 0) := by
    simp [hBump, hCountA, show ¬ ((2 : UInt64) = 0) from by decide,
      not_cap_lt_two hCap]
  have hFreeEq :
      mFree (mAlloc mem a).1 a 2 =
        (mWriteField
          (mWriteField
            (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
            a.cursor 0 (packCursor 2 2))
          (liveField a) 0 0, 2) := by
    unfold mFree
    rw [if_neg hguard]
    simp [hBump, hFree, hCountA]
  refine ⟨by simp [hFreeEq], ?_, ?_, ?_⟩
  · have := mReadField_write_same
      (mWriteField
        (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
        a.cursor 0 (packCursor 2 2))
      (liveField a) 0 0 w.liveW w.hl
    simpa [hFreeEq, mLiveCount, liveField] using this
  · have h1 := mReadField_write_other
      (mWriteField
        (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
        a.cursor 0 (packCursor 2 2))
      a.cursor (liveField a) 0 0 0 w.hc w.hl w.live_ne_cursor.symm
    have h2 := mReadField_write_same
      (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
      a.cursor 0 (packCursor 2 2) w.cursorW w.hc
    simpa [hFreeEq, mCursor] using h1.trans h2
  · have h1 := mReadField_write_other
      (mWriteField
        (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
        a.cursor 0 (packCursor 2 2))
      (slotsField a) (liveField a) 2 0 0 w.hs w.hl w.live_ne_slot2.symm
    have h2 := mReadField_write_other
      (mWriteField (mAlloc mem a).1 (slotsField a) 2 0)
      (slotsField a) a.cursor 2 0 (packCursor 2 2) w.hs w.hc w.cursor_ne_slot2.symm
    have h3 := mReadField_write_same
      (mAlloc mem a).1 (slotsField a) 2 0 w.slot2W w.hs
    simpa [hFreeEq, mSlotWord] using (h1.trans h2).trans h3

/-- SF-5a: after bump-alloc + free of that index, the next alloc returns the same index. -/
theorem mAlloc_free_alloc_same
    (mem : AccountWords) (a : Allocator) (w : AllocWords a)
    (hCap : (2 : UInt64) ≤ UInt64.ofNat a.slots.capacity)
    (hCount : mLiveCount mem a = 0)
    (hCursor : mCursor mem a = packCursor 1 0) :
    (mAlloc (mFree (mAlloc mem a).1 a 2).1 a).2 = 2 := by
  have hF := mFree_after_bump_first mem a w hCap hCount hCursor
  -- Name the post-free memory once so `unfold` does not explode.
  generalize hmemF : (mFree (mAlloc mem a).1 a 2).1 = memF
  have hCountF : mLiveCount memF a = 0 := by
    simpa [hmemF.symm] using hF.2.1
  have hCursorF : mCursor memF a = packCursor 2 2 := by
    simpa [hmemF.symm] using hF.2.2.1
  have hSlotF : mSlotWord memF a 2 = 0 := by
    simpa [hmemF.symm] using hF.2.2.2
  have hBump : unpackBump (mCursor memF a) = 2 := by
    simpa [hCursorF] using unpack_pack_2_2.1
  have hFree : unpackFreeHead (mCursor memF a) = 2 := by
    simpa [hCursorF] using unpack_pack_2_2.2
  have hFull : ¬ (UInt64.ofNat a.slots.capacity ≤ mLiveCount memF a) := by
    simpa [hCountF] using not_cap_le_zero hCap
  have hNe : unpackFreeHead (mCursor memF a) ≠ 0 := by
    simp [hFree]
  have hAlloc :
      mAlloc memF a =
        (mWriteField
          (mWriteField memF a.cursor 0 (packCursor 2 0))
          (liveField a) 0 1, 2) := by
    unfold mAlloc
    rw [if_neg hFull, if_pos hNe]
    simp [hFree, hBump, hCountF, hSlotF, pack_2_0]
  have : (mAlloc memF a).2 = 2 := by simp [hAlloc]
  simpa [← hmemF] using this

end ProofForge.Svm.Sdk.AllocatorModel
