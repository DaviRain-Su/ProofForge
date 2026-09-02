import ProofForge.Core.Collections
import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.StorageEnumerableSet
import ProofForge.Svm.Sdk.OrderedMapModel

/-!
# StorageEnumerableSet model (sf-010)

L2 algebra for the persistent enumerable-set binding:

* active-prefix values list (Lean 0-based; account positions are 1-based)
* `AssocIndex` value→position reverse index (key4 map stand-in; RB → sf-011)
* shared `Core.Collections.BoundedSet` position+1 / swap-remove policy

Delivers: empty contains; insert/full/duplicate fail-closed; empty insert/remove
roundtrips; valueAt OOB → 0; `canValueAt` under well-formed count.
-/

namespace ProofForge.Svm.Sdk.StorageEnumerableSetModel

open ProofForge.Core.Collections
open ProofForge.Svm.Sdk.StorageEnumerableSet
open ProofForge.Svm.Sdk.OrderedMapModel

/-! ## Descriptor L1 parts -/

theorem descriptor_wf_parts {set : Descriptor} (hwf : set.wellFormed = true) :
    set.values.mutableOneBasedWord = true ∧
      set.index.wellFormed = true ∧
      set.positions.mutableOneBasedWord = true := by
  simp only [Descriptor.wellFormed, Bool.and_eq_true] at hwf
  exact ⟨hwf.1.1.1, hwf.1.1.2, hwf.1.2⟩

/-! ## Abstract enumerable-set state -/

structure EnumSet where
  capacity : Nat
  values : List UInt64
  index : AssocIndex
  deriving Repr, Inhabited

@[inline] def EnumSet.count (s : EnumSet) : Nat :=
  s.values.length

def EnumSet.empty (capacity : Nat) : EnumSet :=
  { capacity, values := [], index := ⟨capacity, []⟩ }

def EnumSet.valueAt (s : EnumSet) (index : Nat) : UInt64 :=
  if index < s.count then s.values.getD index 0 else 0

def EnumSet.contains (s : EnumSet) (value : UInt64) : Bool :=
  let pos := s.index.find value 0
  BoundedSet.positionLive pos (UInt64.ofNat s.count) &&
    decide (EnumSet.valueAt s (pos.toNat - 1) = value)

def EnumSet.insert (s : EnumSet) (value : UInt64) : EnumSet × UInt64 :=
  if EnumSet.contains s value then
    (s, 2)
  else if s.capacity ≤ s.count then
    (s, 0)
  else
    let pos : UInt64 := UInt64.ofNat (s.count + 1)
    let ix := (s.index.insert value 0 pos).1
    ({ s with values := s.values ++ [value], index := ix }, 1)

def EnumSet.remove (s : EnumSet) (value : UInt64) : EnumSet × UInt64 :=
  let pos := s.index.find value 0
  if !(BoundedSet.positionLive pos (UInt64.ofNat s.count)) then
    (s, 0)
  else if EnumSet.valueAt s (pos.toNat - 1) != value then
    (s, 0)
  else
    let count := s.count
    let posN := pos.toNat
    let ix0 := (s.index.remove value 0).1
    if posN = count then
      ({ s with values := s.values.dropLast, index := ix0 }, 1)
    else
      let lastVal := s.values.getLast!
      let values' := (s.values.set (posN - 1) lastVal).dropLast
      let ix1 := (ix0.insert lastVal 0 pos).1
      ({ s with values := values', index := ix1 }, 1)

/-! ## Core algebra -/

theorem valueAt_oob (s : EnumSet) (index : Nat) (h : ¬ index < s.count) :
    EnumSet.valueAt s index = 0 := by
  simp [EnumSet.valueAt, h]

theorem contains_empty (cap : Nat) (v : UInt64) :
    EnumSet.contains (EnumSet.empty cap) v = false := by
  simp [EnumSet.contains, EnumSet.empty, AssocIndex.find, BoundedSet.positionLive]

theorem insert_present_two (s : EnumSet) (v : UInt64)
    (h : EnumSet.contains s v = true) :
    EnumSet.insert s v = (s, 2) := by
  simp [EnumSet.insert, h]

theorem insert_full_zero (s : EnumSet) (v : UInt64)
    (habs : EnumSet.contains s v = false) (hfull : s.capacity ≤ s.count) :
    EnumSet.insert s v = (s, 0) := by
  simp [EnumSet.insert, habs, hfull]

theorem remove_absent_zero (s : EnumSet) (v : UInt64)
    (h : s.index.find v 0 = 0) :
    EnumSet.remove s v = (s, 0) := by
  simp [EnumSet.remove, h, BoundedSet.positionLive]

private theorem insert_empty_eq (cap : Nat) (v : UInt64) (hcap : 0 < cap) :
    EnumSet.insert (EnumSet.empty cap) v =
      ({ capacity := cap
         values := [v]
         index := ⟨cap, [{ key0 := v, key1 := 0, slot := 1 }]⟩ }, 1) := by
  have hne : ¬ (cap ≤ 0) := Nat.not_le_of_gt hcap
  have habs :
      EnumSet.contains { capacity := cap, values := [], index := ⟨cap, []⟩ } v = false := by
    simpa [EnumSet.empty] using contains_empty cap v
  simp only [EnumSet.insert, EnumSet.empty, EnumSet.count, AssocIndex.insert, List.length_nil,
    List.append_nil, List.findIdx?_nil, UInt64.ofNat_one]
  rw [habs]
  simp [hne]

private theorem remove_singleton_eq (cap : Nat) (v : UInt64) :
    EnumSet.remove
        { capacity := cap
          values := [v]
          index := ⟨cap, [{ key0 := v, key1 := 0, slot := 1 }]⟩ }
        v =
      ({ capacity := cap, values := [], index := ⟨cap, []⟩ }, 1) := by
  simp only [EnumSet.remove, AssocIndex.find, entryMatches, EnumSet.valueAt, EnumSet.count,
    BoundedSet.positionLive, AssocIndex.remove]
  simp

/-- Empty → insert: code `1`, contains, `valueAt 0 = v`. -/
theorem insert_empty_roundtrip (cap : Nat) (v : UInt64) (hcap : 0 < cap) :
    let r := EnumSet.insert (EnumSet.empty cap) v
    r.2 = 1 ∧ EnumSet.contains r.1 v = true ∧ EnumSet.valueAt r.1 0 = v := by
  have hins := insert_empty_eq cap v hcap
  refine ⟨by simp [hins], ?_, ?_⟩
  · simp [hins, EnumSet.contains, AssocIndex.find, entryMatches, EnumSet.valueAt,
      EnumSet.count, BoundedSet.positionLive]
  · simp [hins, EnumSet.valueAt, EnumSet.count]

/-- Empty → insert → remove last: restores absence. -/
theorem insert_remove_roundtrip_empty (cap : Nat) (v : UInt64) (hcap : 0 < cap) :
    let s1 := (EnumSet.insert (EnumSet.empty cap) v).1
    let r := EnumSet.remove s1 v
    r.2 = 1 ∧ EnumSet.contains r.1 v = false := by
  have hins := insert_empty_eq cap v hcap
  have hrem := remove_singleton_eq cap v
  constructor
  · simp [hins, hrem]
  · have hempty :
        EnumSet.contains { capacity := cap, values := [], index := ⟨cap, []⟩ } v = false := by
      simpa [EnumSet.empty] using contains_empty cap v
    simpa [hins, hrem] using hempty

/-- Under a well-formed count, `canValueAt` reduces to `index < count`. -/
theorem canValueAt_of_wf (capacity count index : UInt64)
    (hwf : BoundedSet.countWellFormed capacity count = true) :
    BoundedSet.canValueAt capacity count index = (index < count) := by
  simp [BoundedSet.canValueAt, hwf]

/-- Model `removeAt`: resolve `valueAt` then reuse `remove`. OOB is a no-op `0`. -/
def EnumSet.removeAt (s : EnumSet) (index : Nat) : EnumSet × UInt64 :=
  if index < s.count then EnumSet.remove s (EnumSet.valueAt s index) else (s, 0)

theorem removeAt_oob (s : EnumSet) (index : Nat) (h : ¬ index < s.count) :
    EnumSet.removeAt s index = (s, 0) := by
  simp [EnumSet.removeAt, h]

/-- Model `clear` resets to the empty set of the same capacity. -/
def EnumSet.clear (s : EnumSet) : EnumSet :=
  EnumSet.empty s.capacity

theorem clear_contains_false (s : EnumSet) (v : UInt64) :
    EnumSet.contains (EnumSet.clear s) v = false := by
  simpa [EnumSet.clear] using contains_empty s.capacity v

end ProofForge.Svm.Sdk.StorageEnumerableSetModel
