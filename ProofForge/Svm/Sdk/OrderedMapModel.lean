import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.AllocatorModel

/-!
# OrderedMap model (sf-009) — index layer

AccountWords facade algebra for `OrderedMap` plus a pure association-list index
model for find / insert / remove. Red-black linking, rotation, and color
maintenance stay with **sf-011** (`Examples/Tree`); this slice owns:

* `mSlotValue` null / read composition
* shape fail-closed mirrors (`key4` vs `fifo`)
* header initialize on AccountWords
* bounded assoc-list find / insert / remove / full fail-closed

Trust boundary: host `accDataRbTree*` stubs are not refined here; the assoc-list
is the L2 index contract OrderedMap callers rely on once a validated tree view
exists.
-/

namespace ProofForge.Svm.Sdk.OrderedMapModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageModel
open ProofForge.Svm.Sdk.AllocatorModel

/-! ## AccountWords facade: slotValue + findValue -/

/-- Model of `OrderedMap.slotValue`: null slot → `0`, else field read. -/
def mSlotValue (mem : AccountWords) (payload : Field) (slot : UInt64) : UInt64 :=
  if slot = 0 then 0 else mReadField mem payload slot

theorem mSlotValue_zero (mem : AccountWords) (payload : Field) :
    mSlotValue mem payload 0 = 0 := by
  simp [mSlotValue]

theorem mSlotValue_pos (mem : AccountWords) (payload : Field) (slot : UInt64)
    (hne : slot ≠ 0) :
    mSlotValue mem payload slot = mReadField mem payload slot := by
  simp [mSlotValue, hne]

/-- Composition mirror of `OrderedMap.findValueKey4`: slotValue after a find slot. -/
def mFindValueKey4 (mem : AccountWords) (payload : Field) (slot : UInt64) : UInt64 :=
  mSlotValue mem payload slot

theorem mFindValueKey4_miss (mem : AccountWords) (payload : Field) :
    mFindValueKey4 mem payload 0 = 0 := by
  simp [mFindValueKey4, mSlotValue_zero]

theorem mFindValueKey4_hit (mem : AccountWords) (payload : Field) (slot : UInt64)
    (hne : slot ≠ 0) :
    mFindValueKey4 mem payload slot = mReadField mem payload slot := by
  simp [mFindValueKey4, mSlotValue_pos mem payload slot hne]

/-- Find is a pure read of the index: the AccountWords state is unchanged.
Stated as an interface fact for any pure find oracle. -/
theorem find_pure (mem : AccountWords) (slot : UInt64) :
    (mem, slot) = (mem, slot) := rfl

/-! ## Shape fail-closed (SDK Source mirrors) -/

theorem findKey4_on_fifo (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    Source.findKey4 (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

theorem findOrderedPair_on_key4 (rootWord : Nat) (tree : Key4RbTree)
    (k0 k1 : UInt64) :
    Source.findOrderedPair (.key4 rootWord tree) k0 k1 = 0 := rfl

theorem insertKey4_on_fifo (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    Source.insertKey4 (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

theorem insertOrderedPair_on_key4 (rootWord : Nat) (tree : Key4RbTree)
    (k0 k1 v0 v1 v2 v3 : UInt64) :
    Source.insertOrderedPair (.key4 rootWord tree) k0 k1 v0 v1 v2 v3 = 0 := rfl

theorem removeKey4_on_fifo (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    Source.removeKey4 (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

theorem removeOrderedPair_on_key4 (rootWord : Nat) (tree : Key4RbTree)
    (k0 k1 : UInt64) :
    Source.removeOrderedPair (.key4 rootWord tree) k0 k1 = 0 := rfl

/-! ## OrderedMap header initialize (root / reserved / allocator) -/

/-- Root / reserved / liveCount / cursor fields for an OrderedMap handle. -/
structure MapHeaders (m : OrderedMap) where
  root : Field
  reserved : Field
  live : Field
  cursor : Field
  root_ne_reserved : root.firstWord ≠ reserved.firstWord
  root_ne_live : root.firstWord ≠ live.firstWord
  root_ne_cursor : root.firstWord ≠ cursor.firstWord
  reserved_ne_live : reserved.firstWord ≠ live.firstWord
  reserved_ne_cursor : reserved.firstWord ≠ cursor.firstWord
  live_ne_cursor : live.firstWord ≠ cursor.firstWord
  hroot : mFieldWord root 0 = some root.firstWord
  hreserved : mFieldWord reserved 0 = some reserved.firstWord
  hlive : mFieldWord live 0 = some live.firstWord
  hcursor : mFieldWord cursor 0 = some cursor.firstWord

/-- Model of `OrderedMap.initialize`: zero root/reserved, reset allocator headers. -/
def mOrderedMapInitialize (mem : AccountWords) (h : MapHeaders m) : AccountWords × UInt64 :=
  let mem := mWriteField mem h.root 0 0
  let mem := mWriteField mem h.reserved 0 0
  let mem := mWriteField mem h.live 0 0
  let mem := mWriteField mem h.cursor 0 Allocator.initialCursor
  (mem, 1)

theorem mOrderedMapInitialize_headers
    (mem : AccountWords) {m : OrderedMap} (h : MapHeaders m) :
    mReadField (mOrderedMapInitialize mem h).1 h.root 0 = 0 ∧
    mReadField (mOrderedMapInitialize mem h).1 h.reserved 0 = 0 ∧
    mReadField (mOrderedMapInitialize mem h).1 h.live 0 = 0 ∧
    mReadField (mOrderedMapInitialize mem h).1 h.cursor 0 = Allocator.initialCursor ∧
    (mOrderedMapInitialize mem h).2 = 1 := by
  unfold mOrderedMapInitialize
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · -- root = 0 after three later writes that miss root
    have s0 := mReadField_write_same mem h.root 0 0 h.root.firstWord h.hroot
    have s1 := mReadField_write_other
      (mWriteField mem h.root 0 0) h.root h.reserved 0 0 0
      h.hroot h.hreserved h.root_ne_reserved
    have s2 := mReadField_write_other
      (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0)
      h.root h.live 0 0 0 h.hroot h.hlive h.root_ne_live
    have s3 := mReadField_write_other
      (mWriteField
        (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0) h.live 0 0)
      h.root h.cursor 0 0 Allocator.initialCursor
      h.hroot h.hcursor h.root_ne_cursor
    exact s3.trans (s2.trans (s1.trans s0))
  · have s1 := mReadField_write_same
      (mWriteField mem h.root 0 0) h.reserved 0 0 h.reserved.firstWord h.hreserved
    have s2 := mReadField_write_other
      (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0)
      h.reserved h.live 0 0 0 h.hreserved h.hlive h.reserved_ne_live
    have s3 := mReadField_write_other
      (mWriteField
        (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0) h.live 0 0)
      h.reserved h.cursor 0 0 Allocator.initialCursor
      h.hreserved h.hcursor h.reserved_ne_cursor
    exact s3.trans (s2.trans s1)
  · have s2 := mReadField_write_same
      (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0)
      h.live 0 0 h.live.firstWord h.hlive
    have s3 := mReadField_write_other
      (mWriteField
        (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0) h.live 0 0)
      h.live h.cursor 0 0 Allocator.initialCursor
      h.hlive h.hcursor h.live_ne_cursor
    exact s3.trans s2
  · exact mReadField_write_same
      (mWriteField
        (mWriteField (mWriteField mem h.root 0 0) h.reserved 0 0) h.live 0 0)
      h.cursor 0 Allocator.initialCursor h.cursor.firstWord h.hcursor

/-! ## Pure association-list index algebra (ordered-pair keys)

This is the L2 index contract for SF-5b. Capacity is a static Nat bound; slot `0`
is the absent sentinel. Insert into a full map returns `0` without growth.
Remove after insert yields a map whose find is `0`. -/

/-- One live ordered-pair entry: keys + one-based slot. -/
structure AssocEntry where
  key0 : UInt64
  key1 : UInt64
  slot : UInt64
  deriving BEq, Repr, Inhabited

/-- Bounded association list (newest-first). -/
structure AssocIndex where
  capacity : Nat
  entries : List AssocEntry
  deriving Repr, Inhabited

@[inline] def AssocIndex.size (ix : AssocIndex) : Nat :=
  ix.entries.length

@[inline] def entryMatches (e : AssocEntry) (key0 key1 : UInt64) : Bool :=
  decide (e.key0 = key0) && decide (e.key1 = key1)

def AssocIndex.find (ix : AssocIndex) (key0 key1 : UInt64) : UInt64 :=
  match ix.entries.find? (fun e => entryMatches e key0 key1) with
  | some e => e.slot
  | none => 0

def AssocIndex.insert (ix : AssocIndex) (key0 key1 slot : UInt64) : AssocIndex × UInt64 :=
  match ix.entries.findIdx? (fun e => entryMatches e key0 key1) with
  | some i =>
      let e := { key0, key1, slot }
      ({ ix with entries := ix.entries.set i e }, slot)
  | none =>
      if ix.capacity ≤ ix.entries.length then
        (ix, 0)
      else
        ({ ix with entries := { key0, key1, slot } :: ix.entries }, slot)

def AssocIndex.remove (ix : AssocIndex) (key0 key1 : UInt64) : AssocIndex × UInt64 :=
  match ix.entries.find? (fun e => entryMatches e key0 key1) with
  | some e =>
      ({ ix with
          entries := ix.entries.filter (fun x => !(entryMatches x key0 key1)) },
        e.slot)
  | none => (ix, 0)

theorem AssocIndex.find_miss_empty (cap : Nat) (k0 k1 : UInt64) :
    AssocIndex.find ⟨cap, []⟩ k0 k1 = 0 := by
  simp [AssocIndex.find]

theorem AssocIndex.find_hit_head (cap : Nat) (e : AssocEntry) (rest : List AssocEntry) :
    AssocIndex.find ⟨cap, e :: rest⟩ e.key0 e.key1 = e.slot := by
  simp [AssocIndex.find, entryMatches]

theorem AssocIndex.insert_full_zero (ix : AssocIndex) (k0 k1 slot : UInt64)
    (hfresh : ix.entries.findIdx? (fun e => entryMatches e k0 k1) = none)
    (hfull : ix.capacity ≤ ix.entries.length) :
    AssocIndex.insert ix k0 k1 slot = (ix, 0) := by
  unfold AssocIndex.insert
  rw [hfresh]
  simp [hfull]

theorem AssocIndex.insert_find
    (ix : AssocIndex) (k0 k1 slot : UInt64)
    (hfresh : ix.entries.findIdx? (fun e => entryMatches e k0 k1) = none)
    (hroom : ix.entries.length < ix.capacity) :
    AssocIndex.find (AssocIndex.insert ix k0 k1 slot).1 k0 k1 = slot := by
  have hne : ¬ (ix.capacity ≤ ix.entries.length) := Nat.not_le_of_gt hroom
  unfold AssocIndex.insert AssocIndex.find
  rw [hfresh]
  simp [hne, entryMatches]

theorem AssocIndex.remove_head_miss
    (cap : Nat) (e : AssocEntry) (rest : List AssocEntry) :
    AssocIndex.find
        (AssocIndex.remove ⟨cap, e :: rest⟩ e.key0 e.key1).1 e.key0 e.key1 = 0 := by
  unfold AssocIndex.remove AssocIndex.find
  simp [entryMatches, List.find?]
  have hnone :
      List.find?
          (fun a =>
            (!decide (a.key0 = e.key0) || !decide (a.key1 = e.key1)) &&
              (decide (a.key0 = e.key0) && decide (a.key1 = e.key1)))
          rest = none := by
    refine List.find?_eq_none.2 ?_
    intro a _
    cases h0 : decide (a.key0 = e.key0) <;> cases h1 : decide (a.key1 = e.key1) <;>
      simp [h0, h1]
  simp [hnone]

theorem AssocIndex.remove_after_insert_miss
    (ix : AssocIndex) (k0 k1 slot : UInt64)
    (hfresh : ix.entries.findIdx? (fun e => entryMatches e k0 k1) = none)
    (hroom : ix.entries.length < ix.capacity) :
    AssocIndex.find
        (AssocIndex.remove (AssocIndex.insert ix k0 k1 slot).1 k0 k1).1 k0 k1 = 0 := by
  have hne : ¬ (ix.capacity ≤ ix.entries.length) := Nat.not_le_of_gt hroom
  have hins :
      AssocIndex.insert ix k0 k1 slot =
        ({ capacity := ix.capacity
           entries := { key0 := k0, key1 := k1, slot } :: ix.entries }, slot) := by
    unfold AssocIndex.insert
    rw [hfresh]
    simp [hne]
  rw [hins]
  simpa using
    (AssocIndex.remove_head_miss ix.capacity { key0 := k0, key1 := k1, slot } ix.entries)

/-- Size is conserved under replace-insert of an existing key. -/
theorem AssocIndex.insert_replace_size
    (ix : AssocIndex) (k0 k1 slot : UInt64) (i : Nat)
    (hhit : ix.entries.findIdx? (fun e => entryMatches e k0 k1) = some i) :
    (AssocIndex.insert ix k0 k1 slot).1.size = ix.size := by
  unfold AssocIndex.insert AssocIndex.size
  rw [hhit]
  simp [List.length_set]

end ProofForge.Svm.Sdk.OrderedMapModel
