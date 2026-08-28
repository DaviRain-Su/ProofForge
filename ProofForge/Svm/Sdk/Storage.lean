import ProofForge.Attr
import ProofForge.Svm.AccountStorage
import ProofForge.Svm.AccountStorage.Source

/-!
# SVM SDK persistent-storage facade

Reusable account-resident container handles composed from the existing
`Svm.AccountStorage` descriptors and `Svm.AccountStorage.Source` facade. This module owns
no new SVM operation, component, IR constructor, or emitter case: every operation erases to
the same checked account load/store and bounded tree/allocator routines that
`AccountStorage.Source` already lowers to.

## Physical-state contract

Every persistent value in this facade is a `u64` account word addressed by an explicit
one-based slot index into a static `Region` (`account`, `baseWord`, `strideWords`,
`capacity`, `indexBase`, `access`). The integer `0` is the universal null sentinel: map
lookups, allocator handles, vector positions, and queue heads all use `0` to mean "absent",
and the one-based read/write stubs reject it before normalization. There is no native
pointer, no Lean `Array`/`Map` in persistent state, no invocation heap object, and no
runtime-selected geometry; all capacities and offsets are compile-time descriptor data that
is erased during extraction.

## Fail-closed policy

- Expected boundary conditions (empty pop/peek, full push, missing key, null slot) return
  the `0` sentinel without mutating account state.
- Malformed conditions (index beyond static capacity, unwritable or foreign account,
  `data_len` too small) still abort inside the target-owned checked stubs with `Custom(1)`.
- `Allocator.free` requires the caller to pass a currently allocated one-based slot. It rejects
  null, never-allocated, and empty-allocator releases without mutation; detecting a duplicate free
  requires an application-owned occupancy bit and remains an explicit caller contract.
-/

namespace ProofForge.Svm.Sdk.Storage

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source

/-! ## Shared scalar-header contract -/

/-- One writable program-owned u64 header word in the same account as a body region. Queue,
vector, and allocator headers all share this predicate so their fail-closed geometry rules
cannot drift apart. -/
def scalarHeaderWellFormed (header : Field) (bodyAccount : Nat)
    (accountLimit : Nat := 64) : Bool :=
  header.wellFormed accountLimit && header.widthWords == 1 &&
    header.region.account == bodyAccount && header.region.account > 0 &&
    header.region.strideWords == 1 && header.region.capacity == 1 &&
    header.region.indexBase == .zero &&
    header.region.access == Access.programOwnedMutable

/-- Static capacity ceiling shared by SDK containers. It keeps header arithmetic inside u64
with room for the one-based translation; the checked stubs still enforce the real account
`data_len` per access. -/
def containerCapacityLimit : Nat := 65536

/-! ## POD field handles -/

/-- A named one-based POD word: one scalar payload column over a fixed record region. The
descriptor is erased at extraction; only the checked load/store remains. -/
structure PodField where
  field : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] PodField.field

/-- Validate the POD column: one writable, program-owned, one-based word per record slot. -/
def PodField.wellFormed (pod : PodField) (accountLimit : Nat := 64) : Bool :=
  pod.field.mutableOneBasedWord accountLimit && pod.field.region.account > 0 &&
    pod.field.region.capacity ≤ containerCapacityLimit

/-- Read the POD word at one-based `slot`. `slot = 0` is the null sentinel and fails closed
inside the target stub; callers guard expected-absent reads themselves. -/
@[pf_inline] def PodField.readAt (pod : PodField) (slot : UInt64) : UInt64 :=
  read pod.field slot

/-- Write the POD word at one-based `slot`. The target requires a writable, program-owned
account and a final byte inside `data_len`. Successful writes return `value`. -/
@[pf_inline] def PodField.writeAt (pod : PodField) (slot value : UInt64) : UInt64 :=
  let _ := write pod.field slot value
  value

/-! ## Fixed-capacity vector -/

/-- Account-resident bounded vector: a one-based payload column plus one scalar `count`
header. Positions are one-based indexes `1..count`; `count` never exceeds the static region
capacity. Persistent state is account words and indexes only. -/
structure BoundedVec where
  slots : Field
  count : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] BoundedVec.slots BoundedVec.count

/-- Construct a one-word-payload vector with a scalar count header placed before the body. -/
@[pf_inline] def BoundedVec.oneBased
    (account countWord slotsBaseWord capacity : Nat) : BoundedVec :=
  { slots := Field.oneBased account slotsBaseWord 1 capacity
    count := Field.scalar account countWord }

/-- Static capacity of the backing region. Compile-time descriptor data, never runtime state. -/
@[pf_inline] def BoundedVec.capacity (vec : BoundedVec) : UInt64 :=
  UInt64.ofNat vec.slots.region.capacity

def BoundedVec.wellFormed (vec : BoundedVec) (accountLimit : Nat := 64) : Bool :=
  vec.slots.mutableOneBasedWord accountLimit && vec.slots.region.account > 0 &&
    vec.slots.region.capacity ≤ containerCapacityLimit &&
    scalarHeaderWellFormed vec.count vec.slots.region.account accountLimit &&
    vec.count.firstWord + 1 ≤ vec.slots.firstWord

/-- Number of live positions. Stored as an account word; `0` is the empty vector. -/
@[pf_inline] def BoundedVec.size (vec : BoundedVec) : UInt64 :=
  read vec.count 0

/-- Read position `position` (one-based). Out-of-range and null positions return the `0`
sentinel without touching the account. -/
@[pf_inline] def BoundedVec.getAt (vec : BoundedVec) (position : UInt64) : UInt64 :=
  let size := BoundedVec.size vec
  if position = 0 || size < position then 0 else read vec.slots position

/-- Overwrite position `position` (one-based). Out-of-range positions leave the vector
unchanged and return `0`; a successful write returns `value`. -/
@[pf_inline] def BoundedVec.setAt (vec : BoundedVec) (position value : UInt64) : UInt64 :=
  let size := BoundedVec.size vec
  if position = 0 || size < position then 0
  else
    let _ := write vec.slots position value
    value

/-- Append `value` at the first free position. A full vector returns `0` and performs no
store; success returns the new one-based position (`count` after the push). -/
@[pf_inline] def BoundedVec.push (vec : BoundedVec) (value : UInt64) : UInt64 :=
  let size := BoundedVec.size vec
  if BoundedVec.capacity vec ≤ size then 0
  else
    let _ := write vec.slots (size + 1) value
    let _ := write vec.count 0 (size + 1)
    size + 1

/-- Remove and return the last position's value. An empty vector returns `0` and performs no
store; the count header shrinks but the popped slot's bytes stay account-resident until the
next push reinitializes them. -/
@[pf_inline] def BoundedVec.pop (vec : BoundedVec) : UInt64 :=
  let size := BoundedVec.size vec
  if size = 0 then 0
  else
    let value := read vec.slots size
    let _ := write vec.count 0 (size - 1)
    value

/-! ## Ordered maps -/

/-- Typed handle over one statically shaped account-resident red-black map (four-word key or
ordered-pair key). Bundles the map with its allocator-derived header contract so
applications stop repeating root/size/cursor geometry. -/
structure OrderedMap where
  map : RbMap
  deriving BEq, Repr, Inhabited

attribute [pf_inline] OrderedMap.map

/-- Validate the ordered map: complete RB topology plus the exact live/free allocator
partition of its one-based slots. -/
def OrderedMap.wellFormed (orderedMap : OrderedMap) (accountLimit : Nat := 64) : Bool :=
  orderedMap.map.wellFormed accountLimit &&
    orderedMap.map.allocator.wellFormed accountLimit

/-- Live key count from the map's allocator header. -/
@[pf_inline] def OrderedMap.count (orderedMap : OrderedMap) : UInt64 :=
  Source.liveCount orderedMap.map

/-- Full in-place tree and allocator validation. Dominating views call this once before
find/insert/remove batches. -/
@[pf_inline] def OrderedMap.validate (orderedMap : OrderedMap) : UInt64 :=
  Source.validate orderedMap.map

/-- The map's one-based slot allocator (shared header layout, `0` null sentinel). -/
@[pf_inline] def OrderedMap.allocator (orderedMap : OrderedMap) : OneBasedAllocator :=
  orderedMap.map.allocator

/-- Read one payload word at a one-based slot returned by a map lookup. `slot = 0` is the
null sentinel and returns `0` without an account access. -/
@[pf_inline] def OrderedMap.slotValue (payload : Field) (slot : UInt64) : UInt64 :=
  if slot = 0 then 0 else read payload slot

/-- Four-word-key lookup: `0` when the key is absent, otherwise its one-based slot. -/
@[pf_inline] def OrderedMap.findKey4 (orderedMap : OrderedMap)
    (key0 key1 key2 key3 : UInt64) : UInt64 :=
  Source.findKey4 orderedMap.map key0 key1 key2 key3

/-- Four-word-key insert under the reject-duplicates policy. Returns the new one-based slot,
or `0` for a duplicate key or exhausted allocator. -/
@[pf_inline] def OrderedMap.insertKey4 (orderedMap : OrderedMap)
    (key0 key1 key2 key3 : UInt64) : UInt64 :=
  Source.insertKey4 orderedMap.map key0 key1 key2 key3

/-- Four-word-key removal. Missing keys are the caller's policy: this returns `0` for both
"absent" and "removed" so callers that care compose `findKey4` first. -/
@[pf_inline] def OrderedMap.removeKey4 (orderedMap : OrderedMap)
    (key0 key1 key2 key3 : UInt64) : UInt64 :=
  Source.removeKey4 orderedMap.map key0 key1 key2 key3

/-- Checked add of two payload words on a four-word-keyed record, inserting a zeroed record
when absent. -/
@[pf_inline] def OrderedMap.checkedAddKey4 (orderedMap : OrderedMap)
    (key0 key1 key2 key3 delta0 delta1 : UInt64) : UInt64 :=
  Source.checkedAddKey4 orderedMap.map key0 key1 key2 key3 delta0 delta1

/-- Composed four-word-key lookup: return the payload word stored at the key's slot, or the
`0` sentinel when the key is absent. No pointer or copied node is formed. -/
@[pf_inline] def OrderedMap.findValueKey4 (orderedMap : OrderedMap) (payload : Field)
    (key0 key1 key2 key3 : UInt64) : UInt64 :=
  let slot := Source.findKey4 orderedMap.map key0 key1 key2 key3
  OrderedMap.slotValue payload slot

/-- Two-word lexicographic lookup: `0` when absent, otherwise the one-based slot. -/
@[pf_inline] def OrderedMap.findOrderedPair (orderedMap : OrderedMap)
    (key0 key1 : UInt64) : UInt64 :=
  Source.findOrderedPair orderedMap.map key0 key1

/-- Resume the stored traversal cursor for a two-word key; `hasCursor = 0` starts a fresh
ordered scan. -/
@[pf_inline] def OrderedMap.cursorOrderedPair (orderedMap : OrderedMap)
    (hasCursor key0 key1 : UInt64) : UInt64 :=
  Source.cursorOrderedPair orderedMap.map hasCursor key0 key1

/-- Ordered-pair insert under the replace-duplicates policy with a four-word payload.
Returns the one-based slot, or `0` when the allocator is exhausted. -/
@[pf_inline] def OrderedMap.insertOrderedPair (orderedMap : OrderedMap)
    (key0 key1 value0 value1 value2 value3 : UInt64) : UInt64 :=
  Source.insertOrderedPair orderedMap.map key0 key1 value0 value1 value2 value3

/-- Ordered-pair removal. -/
@[pf_inline] def OrderedMap.removeOrderedPair (orderedMap : OrderedMap)
    (key0 key1 : UInt64) : UInt64 :=
  Source.removeOrderedPair orderedMap.map key0 key1

/-- Overwrite one payload word at the caller-prevalidated slot of an ordered-pair key, or
remove the whole record when `value = 0`. The slot must have been returned for
`(key0, key1)` by the same validated view in this invocation. -/
@[pf_inline] def OrderedMap.setWordOrRemoveOrderedPair (orderedMap : OrderedMap)
    (payload : Field) (key0 key1 slot value : UInt64) : UInt64 :=
  Source.setWordOrRemoveOrderedPair orderedMap.map payload key0 key1 slot value

/-- Composed ordered-pair lookup: the payload word at the key's slot, or the `0` sentinel
when absent. -/
@[pf_inline] def OrderedMap.findValueOrderedPair (orderedMap : OrderedMap) (payload : Field)
    (key0 key1 : UInt64) : UInt64 :=
  let slot := Source.findOrderedPair orderedMap.map key0 key1
  OrderedMap.slotValue payload slot

/-- First key word at a live one-based slot (ordered-pair maps). -/
@[pf_inline] def OrderedMap.orderedKey0 (orderedMap : OrderedMap) (slot : UInt64) : UInt64 :=
  Source.orderedKey0 orderedMap.map slot

/-- Second key word at a live one-based slot (ordered-pair maps). -/
@[pf_inline] def OrderedMap.orderedKey1 (orderedMap : OrderedMap) (slot : UInt64) : UInt64 :=
  Source.orderedKey1 orderedMap.map slot

/-! ## One-based allocators -/

/-- The allocator handle is the existing account-resident descriptor: a one-based slot region,
a live-count header, and a packed cursor word `(bumpIndex | freeListHead <<< 32)`. Free slots
thread their free-list successor through slot word 0 (the links word for map-shaped regions);
`0` is the end-of-list and null sentinel. No pointer ever leaves the account. -/
abbrev Allocator := OneBasedAllocator

/-- Live slots currently handed out (application-maintained occupancy header). -/
@[pf_inline] def Allocator.liveCount (allocator : Allocator) : UInt64 :=
  read (OneBasedAllocator.liveCount allocator) 0

/-- Bump frontier: every slot `1..bumpIndex` has been allocated at least once. -/
@[pf_inline] def Allocator.bumpIndex (allocator : Allocator) : UInt64 :=
  read allocator.cursor 0 &&& 0xffffffff

/-- Head of the one-based free list, or `0` when empty. -/
@[pf_inline] def Allocator.freeListHead (allocator : Allocator) : UInt64 :=
  read allocator.cursor 0 >>> 32

/-- Recover the allocator handle of an ordered map; the map's links word is slot word 0, so
alloc/free compose with the map's own allocator discipline. -/
@[pf_inline] def Allocator.ofRbMap (map : RbMap) : Allocator := map.allocator

/-- Allocate one one-based slot. Reuses the free-list head when present, otherwise advances
the bump frontier while it is below the static capacity. Returns `0` (and writes nothing)
when the allocator is exhausted. -/
@[pf_inline] def Allocator.alloc (allocator : Allocator) : UInt64 :=
  let capacity := UInt64.ofNat allocator.slots.capacity
  let count := read (OneBasedAllocator.liveCount allocator) 0
  let cursor := read allocator.cursor 0
  let bump : UInt64 := cursor &&& 0xffffffff
  let freeHead : UInt64 := cursor >>> 32
  if capacity ≤ count then 0
  else if freeHead ≠ 0 then
    let next := read { region := allocator.slots } freeHead
    let _ := write allocator.cursor 0 (bump ||| (next <<< 32))
    let _ := write (OneBasedAllocator.liveCount allocator) 0 (count + 1)
    freeHead
  else if bump < capacity then
    let _ := write allocator.cursor 0 ((bump + (1 : UInt64)) ||| (freeHead <<< 32))
    let _ := write (OneBasedAllocator.liveCount allocator) 0 (count + 1)
    bump + 1
  else
    0

/-- Return a currently allocated one-based slot to the free list by threading the previous
head through its word 0. Null, never-allocated, and empty-allocator releases return `0` with no
mutation. Freeing an already-free slot remains a caller contract violation; applications that
cannot establish liveness must pair the allocator with an occupancy field. -/
@[pf_inline] def Allocator.free (allocator : Allocator) (slot : UInt64) : UInt64 :=
  let capacity := UInt64.ofNat allocator.slots.capacity
  let count := read (OneBasedAllocator.liveCount allocator) 0
  let cursor := read allocator.cursor 0
  let bump : UInt64 := cursor &&& 0xffffffff
  let freeHead : UInt64 := cursor >>> 32
  if slot = 0 || bump < slot || capacity < slot || count = 0 then 0
  else
    let _ := write { region := allocator.slots } slot freeHead
    let _ := write allocator.cursor 0 (bump ||| (slot <<< 32))
    let _ := write (OneBasedAllocator.liveCount allocator) 0 (count - 1)
    slot

end ProofForge.Svm.Sdk.Storage
