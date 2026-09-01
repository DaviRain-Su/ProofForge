import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.StorageBitSet

/-!
# StorageBitSet model (sf-005)

Pure packed-word algebra + AccountWords bridge for `Sdk.StorageBitSet`.
-/

namespace ProofForge.Svm.Sdk.StorageBitSetModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageModel
open ProofForge.Svm.Sdk.StorageBitSet

/-! ## L1 wf parts + geometry -/

theorem bitSet_wf_parts {set : BitSet} (hwf : set.wellFormed = true) :
    (0 : Nat) < set.bitCapacity ∧
    wordCount set.bitCapacity ≤ containerCapacityLimit ∧
    set.words.mutableOneBasedWord = true ∧
    set.words.region.account > 0 ∧
    set.words.region.capacity = wordCount set.bitCapacity := by
  simp only [BitSet.wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwf
  exact ⟨hwf.1.1.1.1, hwf.1.1.1.2, hwf.1.1.2, hwf.1.2, hwf.2⟩

theorem wordCount_eq (bits : Nat) :
    wordCount bits = (bits + 63) / 64 :=
  rfl

theorem bitSet_wf_indexBase {set : BitSet} (hwf : set.wellFormed = true) :
    set.words.region.indexBase = IndexBase.one := by
  have parts := mutableOneBased_wf_parts (h := (bitSet_wf_parts hwf).2.2.1)
  exact indexBase_beq_one_eq parts.2.2.1

theorem mFieldWord_bitSet_words {set : BitSet} (hwf : set.wellFormed = true)
    (slot : UInt64)
    (h1 : (1 : Nat) ≤ slot.toNat) (h2 : slot.toNat ≤ set.words.region.capacity) :
    mFieldWord set.words slot =
      some (set.words.firstWord + (slot.toNat - 1) * set.words.region.strideWords) := by
  have hidx := bitSet_wf_indexBase hwf
  unfold mFieldWord
  rw [hidx]
  simp only [h1, h2, and_true, if_true, Field.firstWord]

/-! ## Pure Nat / UInt64 bit helpers -/

private theorem nat_and_or_right_eq (w m : Nat) : (w ||| m) &&& m = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_or, Nat.testBit_and]
  cases Nat.testBit m i <;> simp

private theorem nat_xor_xor_cancel (w m : Nat) : (w ^^^ m) ^^^ m = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases h₁ : Nat.testBit w i <;> cases h₂ : Nat.testBit m i <;> simp [h₁, h₂, Nat.testBit_xor]

private theorem u64_and_or_right_eq (w m : UInt64) : (w ||| m) &&& m = m := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_and, UInt64.toNat_or]
  exact nat_and_or_right_eq _ _

private theorem u64_xor_xor_cancel (w m : UInt64) : (w ^^^ m) ^^^ m = w := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_xor, UInt64.toNat_xor]
  exact nat_xor_xor_cancel _ _

private theorem maskOf_ne_zero (index : UInt64) : maskOf index ≠ 0 := by
  intro h
  simp only [maskOf] at h
  unfold ProofForge.Core.Collections.BoundedBitSet.maskOf at h
  have h1 : ((1 : UInt64) <<< (index % 64)).toNat = 0 := by rw [h]; rfl
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one] at h1
  have hk : (index % 64).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have hpow_eq : (1 : Nat) <<< ((index % 64).toNat % 64)
      = 2 ^ ((index % 64).toNat % 64) := by
    simp [Nat.shiftLeft_eq]
  have hlt : (1 : Nat) <<< ((index % 64).toNat % 64) < 2 ^ 64 := by
    rw [hpow_eq]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  have hmod64 : (1 : Nat) <<< ((index % 64).toNat % 64) % (2 ^ 64)
      = (1 : Nat) <<< ((index % 64).toNat % 64) := Nat.mod_eq_of_lt hlt
  have hne : (1 : Nat) <<< ((index % 64).toNat % 64) ≠ 0 := by
    rw [hpow_eq]
    exact Nat.ne_of_gt (Nat.pow_pos (by decide : (0 : Nat) < 2))
  exact hne (hmod64 ▸ h1)

/-! ## Pure packed-word algebra -/

theorem insertOf_contains (word index : UInt64) :
    containsOf (insertOf word index) index = true := by
  change ((word ||| maskOf index) &&& maskOf index != 0) = true
  have h : (word ||| maskOf index) &&& maskOf index = maskOf index :=
    u64_and_or_right_eq _ _
  simp only [h]
  exact (bne_iff_ne (a := maskOf index) (b := (0 : UInt64))).mpr (maskOf_ne_zero index)

theorem toggleOf_involutive (word index : UInt64) :
    toggleOf (toggleOf word index) index = word := by
  change (word ^^^ maskOf index) ^^^ maskOf index = word
  exact u64_xor_xor_cancel _ _

theorem removeOf_and_mask (word index : UInt64) :
    removeOf word index &&& maskOf index = 0 := by
  change (word &&& ~~~maskOf index) &&& maskOf index = 0
  apply UInt64.toBitVec_inj.1
  rw [UInt64.toBitVec_and, UInt64.toBitVec_and, UInt64.toBitVec_not]
  rw [BitVec.and_assoc]
  have hcomm : (~~~(maskOf index).toBitVec &&& (maskOf index).toBitVec) = 0 := by
    rw [BitVec.and_comm, BitVec.and_not_self]
  rw [hcomm]
  simp [BitVec.and_zero]

theorem removeOf_not_contains (word index : UInt64) :
    containsOf (removeOf word index) index = false := by
  change (removeOf word index &&& maskOf index != 0) = false
  have h := removeOf_and_mask word index
  simp only [h]
  decide

/-! ## AccountWords model

模型用正向 `inRange` 守卫（与 SDK `if !inRange` 语义对偶），便于分支代数。 -/

def mBitSetContains (mem : AccountWords) (set : BitSet) (index : UInt64) : UInt64 :=
  if inRange set.capacity index then
    let word := mReadField mem set.words (wordSlotOf index)
    if word &&& maskOf index = 0 then 0 else 1
  else
    0

def mBitSetInsert (mem : AccountWords) (set : BitSet) (index : UInt64) :
    AccountWords × UInt64 :=
  if inRange set.capacity index then
    let slot := wordSlotOf index
    let word := mReadField mem set.words slot
    if word &&& maskOf index = 0 then
      (mWriteField mem set.words slot (insertOf word index), 1)
    else
      (mem, 0)
  else
    (mem, 0)

def mBitSetRemove (mem : AccountWords) (set : BitSet) (index : UInt64) :
    AccountWords × UInt64 :=
  if inRange set.capacity index then
    let slot := wordSlotOf index
    let word := mReadField mem set.words slot
    if word &&& maskOf index = 0 then
      (mem, 0)
    else
      (mWriteField mem set.words slot (removeOf word index), 1)
  else
    (mem, 0)

def mBitSetToggle (mem : AccountWords) (set : BitSet) (index : UInt64) :
    AccountWords × UInt64 :=
  if inRange set.capacity index then
    let slot := wordSlotOf index
    let word := mReadField mem set.words slot
    if word &&& maskOf index = 0 then
      (mWriteField mem set.words slot (insertOf word index), 1)
    else
      (mWriteField mem set.words slot (removeOf word index), 0)
  else
    (mem, 0)

/-- OOB insert 不写。 -/
theorem mBitSetInsert_oob_noop (mem : AccountWords) (set : BitSet) (index : UInt64)
    (h : inRange set.capacity index = false) :
    mBitSetInsert mem set index = (mem, 0) := by
  simp [mBitSetInsert, h]

/-- OOB remove 不写。 -/
theorem mBitSetRemove_oob_noop (mem : AccountWords) (set : BitSet) (index : UInt64)
    (h : inRange set.capacity index = false) :
    mBitSetRemove mem set index = (mem, 0) := by
  simp [mBitSetRemove, h]

/-- OOB toggle 不写。 -/
theorem mBitSetToggle_oob_noop (mem : AccountWords) (set : BitSet) (index : UInt64)
    (h : inRange set.capacity index = false) :
    mBitSetToggle mem set index = (mem, 0) := by
  simp [mBitSetToggle, h]

/-- OOB contains 得 0。 -/
theorem mBitSetContains_oob (mem : AccountWords) (set : BitSet) (index : UInt64)
    (h : inRange set.capacity index = false) :
    mBitSetContains mem set index = 0 := by
  simp [mBitSetContains, h]

/-- 缺位 insert 后 contains = 1（需槽位词合法）。 -/
theorem mBitSetInsert_absent_readback (mem : AccountWords) (set : BitSet) (index : UInt64)
    (hwf : set.wellFormed = true)
    (hin : inRange set.capacity index = true)
    (habsent : mReadField mem set.words (wordSlotOf index) &&& maskOf index = 0)
    (hslot1 : (1 : Nat) ≤ (wordSlotOf index).toNat)
    (hslot2 : (wordSlotOf index).toNat ≤ set.words.region.capacity) :
    (mBitSetInsert mem set index).2 = 1 ∧
    mBitSetContains (mBitSetInsert mem set index).1 set index = 1 := by
  have hws := mFieldWord_bitSet_words hwf (wordSlotOf index) hslot1 hslot2
  have hins :
      mBitSetInsert mem set index =
        (mWriteField mem set.words (wordSlotOf index)
          (insertOf (mReadField mem set.words (wordSlotOf index)) index), 1) := by
    simp [mBitSetInsert, hin, habsent]
  constructor
  · simp [hins]
  · rw [hins]
    simp only [mBitSetContains, hin, ↓reduceIte]
    have hread := mReadField_write_same mem set.words (wordSlotOf index)
      (insertOf (mReadField mem set.words (wordSlotOf index)) index) _ hws
    rw [hread]
    have hcont := insertOf_contains (mReadField mem set.words (wordSlotOf index)) index
    have hne : insertOf (mReadField mem set.words (wordSlotOf index)) index &&& maskOf index ≠ 0 := by
      change ((insertOf (mReadField mem set.words (wordSlotOf index)) index &&&
          maskOf index) != 0) = true at hcont
      exact (bne_iff_ne
        (a := insertOf (mReadField mem set.words (wordSlotOf index)) index &&& maskOf index)
        (b := (0 : UInt64))).mp hcont
    simp only [if_neg hne]

/-- 已存在位 insert 不写，返回 0。 -/
theorem mBitSetInsert_present_noop (mem : AccountWords) (set : BitSet) (index : UInt64)
    (hin : inRange set.capacity index = true)
    (hpresent : mReadField mem set.words (wordSlotOf index) &&& maskOf index ≠ 0) :
    mBitSetInsert mem set index = (mem, 0) := by
  simp [mBitSetInsert, hin, hpresent]

/-- 在位 remove 后 contains = 0。 -/
theorem mBitSetRemove_present_readback (mem : AccountWords) (set : BitSet) (index : UInt64)
    (hwf : set.wellFormed = true)
    (hin : inRange set.capacity index = true)
    (hpresent : mReadField mem set.words (wordSlotOf index) &&& maskOf index ≠ 0)
    (hslot1 : (1 : Nat) ≤ (wordSlotOf index).toNat)
    (hslot2 : (wordSlotOf index).toNat ≤ set.words.region.capacity) :
    (mBitSetRemove mem set index).2 = 1 ∧
    mBitSetContains (mBitSetRemove mem set index).1 set index = 0 := by
  have hws := mFieldWord_bitSet_words hwf (wordSlotOf index) hslot1 hslot2
  have hrm :
      mBitSetRemove mem set index =
        (mWriteField mem set.words (wordSlotOf index)
          (removeOf (mReadField mem set.words (wordSlotOf index)) index), 1) := by
    simp [mBitSetRemove, hin, hpresent]
  constructor
  · simp [hrm]
  · rw [hrm]
    simp only [mBitSetContains, hin, ↓reduceIte]
    have hread := mReadField_write_same mem set.words (wordSlotOf index)
      (removeOf (mReadField mem set.words (wordSlotOf index)) index) _ hws
    rw [hread, removeOf_and_mask]
    simp

end ProofForge.Svm.Sdk.StorageBitSetModel
