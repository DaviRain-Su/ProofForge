import ProofForge.Attr
import ProofForge.Core.Collections
import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.StorageEnumerableSet

/-!
# EVM SDK persistent bounded enumerable UInt64 set (R5-017)

`StorageEnumerableSet` is the reusable *persistent* bounded-enumerable-set policy for EVM
storage, comparable in shape to a bounded `EnumerableSet` of `uint64`: O(1)
contains/insert/remove with swap-remove, plus bounded positional enumeration over the live
prefix. It binds the existing physical state model — ordinary `Vector` extraction plus the
existing hashed `U64Map` component — exactly the way `StorageVec` binds
`Core.Value.BoundedVec`, `StorageRing` binds the queue, and `StorageBitmap` binds the bit set:

- **compile-time capacity**: the backing store is an ordinary `Vector UInt64 capacity` field
  of the consumer's `State` structure, flattened by the existing fixed-vector extraction path
  into `capacity` consecutive static slots (`values_0 … values_<capacity-1>`). There is no
  runtime slot allocator and no pointer; the slot table is fixed at extraction.
- **explicit live count**: one adjacent `UInt64` scalar field is the live-element count. A
  count above the capacity is *malformed* and every mutation fails closed on it.
- **key → position+1 index**: one hashed `U64Map` component maps each live key to `index + 1`;
  a zero means *absent*. Because absence is the exact literal `0` (never "not in the map"),
  the key `0` is an ordinary member with no ambiguity. The map is a compile-time
  `Storage.U64Map` handle (hashed-map namespace), disjoint from the static slot numbering.

## Physical-state invariant

- `values`: a backing table of `capacity` slots; only the active prefix `0..<live>` is
  reachable. Stale values beyond the prefix (and stale values of removed keys) are unreachable.
- `count` (live): `0..capacity`, always `≤ capacity`.
- for a key `k`: `map[k] = 0` ⇒ `k` is absent; `map[k] = i+1` ⇒ `i < live` and
  `values[i] = k`. A nonzero position beyond `live`, or a position whose stored value does not
  equal the key, is *malformed* (forged metadata), not absent: mutations fail closed on it and
  no store is committed.

## Why policy decisions, not returned sets

The current EVM extraction lowers dynamic-index `Vector` reads/writes only when the vector is a
`State` field and the index proof is an explicit `if h : … < capacity` hypothesis in the
consumer (`Examples.Evm.EvmStaticRoster.setSeat`, `Examples.Evm.EvmVecLog.record`), and the hashed-map
component is reached only through the existing `Runtime.evmMapGetU64` / `evmMapSetU64` leaves
against a compile-time `U64Map` base. A generic helper returning an updated set value is not an
extractable shape today, so — exactly like `StorageVec` and `StorageRing` — this module owns
the reusable *decisions and slot/position arithmetic* while applications own the literal
`State` field writes and the explicit map puts:

```lean
-- insert (values[live] = key, map[key] = live+1, then live+1)
if StorageEnumerableSet.absent pos then
  if StorageEnumerableSet.canInsert capacity s.count then
    if h : s.count.toNat < 3 then       -- compiler proof for the physical write
      .ok ({ s with values := s.values.set s.count.toNat key h, count := s.count + 1 },
        Effect.thenTrue (positions.put key (s.count + 1)))
    else .error .malformed              -- unreachable under an admissible decision
  else .error .full
else …
```

The map puts chain as one `UInt64` carrier expression (`put … ||| put …`), the repo's exact
effect-result sequencing (`Sdk.Erc721.burn`, `Examples.Evm.Token.transferFrom`), and stay in the
second component of the consumer's `Except Error (State × …)` result. `Effect.thenTrue` turns
the carrier into a canonical Boolean ABI value.

## Fail-closed policy

| situation | decision result | suggested consumer terminal |
|---|---|---|
| `capacity < count` (malformed count) | every mutation decision is `false` | typed malformed error before any store |
| insert of a live (or forged) key | `canInsert/absent` gates exclude it | typed duplicate error before any store |
| insert when `count = capacity` (full) | `canInsert = false` | typed full / `CapExceeded()` |
| nonzero position `> live` (forged) | `positionLive = false`, `forged = true` | typed malformed error before any store |
| position ≤ live but `values[position-1] ≠ key` | `isPresent = false` | typed malformed error before any store |
| remove of absent key (`map[key] = 0`) | `absent = true` | explicit no-write success (no store at all) |
| get with `live ≤ index` (OOB) | `active = false` | view fallback or typed error |

A rejected or malformed decision returns before any slot write and before any map put, so
under the ordered storage semantics no partial update can be committed.

## Resource contract (worst case, O(1) in every dimension)

Each operation touches a constant number of storage slots, independent of `capacity`; there is
no loop over the backing table. Distinct-slot footprint:

| operation | distinct slots read | slots written | notes |
|---|---|---|---|
| `contains` view | 3 | 0 | `count`, `map[key]`, selected element slot |
| insert | 2 | 3 | reads `count`, `map[key]`; stores `values[live]`, `map[key]`, `count` |
| remove (middle) | 3 | 4 | reads `count`, `map[key]`, element, last; stores `values[i]`, `map[last]`, `map[key]`, `count` |
| remove (last/only) | 3 | 2 | no swap move: stores `map[key]`, `count` |
| `valueAt` view | 2 | 0 | `count` + selected element slot |

Two honest qualifiers: (1) the arithmetic subexpressions (`indexOf`, `lastIndex`,
`removedCount`) are recomputed at each use site instead of cached in a Yul local — a constant
number of ALU ops, and the solc optimizer may CSE them; (2) a consumer's own authorization gate
adds its own footprint (e.g. `Access.requireOwner` reads the three Address limbs of the stored
owner). Cold zero→nonzero SSTORE pricing dominates real gas; the SDK guarantees only the
*shape* — constant, capacity-independent slot count, no iteration.

`clear` is deliberately *not* exposed: honestly resetting every `map[k]` entry to `0` is an
`live`-bounded loop, which this O(1) policy does not provide. Removing keys one by one leaves
stale backing values unreachable, which preserves soundness. Bulk-clearing is an application
decision made with its own explicit compile-time structure.

The descriptor is compile-time data erased before extraction and costs nothing at runtime.
-/

/-- Compile-time descriptor of one persistent bounded enumerable UInt64 set: the fixed backing
`Vector UInt64 capacity` field, the adjacent explicit live-count scalar, and the hashed
key → position+1 map. Handles are extraction-time data erased before runtime; they never appear
in emitted code. -/
structure Descriptor (capacity : Nat) where
  /-- Fixed backing field: flattens to `capacity` consecutive 8-byte slots. -/
  values : Storage.Static.Handle (Vector UInt64 capacity)
  /-- Explicit live count: one 8-byte scalar slot directly after the backing slots. -/
  count : Storage.Static.Handle UInt64
  /-- Hashed key → position+1 namespace. Its base is the consumer's own `Storage.Layout`
  cursor — a separate numbering, disjoint from the static slots handled by this descriptor. -/
  positions : Storage.U64Map
  deriving Repr

/-- Declare the backing vector and its live-count scalar as consecutive static fields, in the
exact order the consumer's `State` structure declares them (`values` first, `count` immediately
after). The map handle is the consumer's existing hashed-map namespace allocation. -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (valuesName countName : String)
    (positions : Storage.U64Map) (capacity : Nat) : Storage.Static.Allocated (Descriptor capacity) :=
  let values := layout.array (α := Vector UInt64 capacity) valuesName .u64 capacity
  let count := values.next.uint64 countName
  { handle := { values := values.handle, count := count.handle, positions }, next := count.next }

/-- Descriptor-level validity, checked by focused tests before any extraction is trusted:
positive codec-representable capacity, exactly the declared one-slot-per-element UInt64 array
handle of length `capacity`, and the count scalar occupying the slot directly after the last
backing slot. The hashed-map namespace is validated by its own component and by the consumer's
`Storage.Layout` cursor; static slots and hashed-map bases never share a numbering. -/
def Descriptor.wellFormed {capacity : Nat} (set : Descriptor capacity) : Bool :=
  0 < capacity && capacity < UInt32.size &&
    set.values.wellFormed && set.count.wellFormed &&
    set.values.spec == Storage.Static.Spec.arrayLeaves .u64 capacity &&
    set.count.spec == Storage.Static.Spec.leaf .u64 &&
    set.count.slot? == some (set.values.baseSlot + capacity)

/-! ## Runtime policy decisions

All decisions are pure `pf_inline` functions over explicit runtime scalars (`count`,
`position`, `index`, and the already-loaded `stored` element) and the compile-time `capacity`
scalar. `capacity` must decode to a compile-time literal at every call site (consumers expose
one `@[pf_inline]` capacity literal for it). Every mutation decision rechecks `wellFormed`, so
a malformed count fails closed even if storage was corrupted outside the component. The
`position` value is what the map reports for the key; it is *observed evidence*, validated
below before any physical write trusts it. -/

/-- The runtime count is canonical: it never exceeds the compile-time capacity. -/
@[pf_inline] def wellFormed (capacity count : UInt64) : Bool :=
  Core.Collections.BoundedSet.countWellFormed capacity count

/-- No live keys. -/
@[pf_inline] def isEmpty (count : UInt64) : Bool :=
  Core.Collections.BoundedSet.isEmptyCount count

/-- The live keys already occupy every backing slot. -/
@[pf_inline] def isFull (capacity count : UInt64) : Bool :=
  Core.Collections.BoundedSet.isFullCount capacity count

/-! ### Membership (observed-position validation)

For key `k`, the map is read once: `position = map[k]`. `position = 0` is the only absent
evidence. A nonzero position outside `1..count`, or one whose backing element does not equal
`k`, is malformed (forged metadata) — never treated as absent. -/

/-- Map evidence of absence: the exact zero. Key `0` is an ordinary member: a live `0` maps to
`index + 1 ≥ 1`, never to the absent literal. -/
@[pf_inline] def absent (position : UInt64) : Bool :=
  Core.Collections.BoundedSet.absentPosition position

/-- A nonzero position that addresses a live element: `1 ≤ position ≤ count`. -/
@[pf_inline] def positionLive (position count : UInt64) : Bool :=
  Core.Collections.BoundedSet.positionLive position count

/-- A nonzero position outside the live range: forged map metadata over canonical storage.
Mutations must fail closed on it (never write, never repair). -/
@[pf_inline] def forged (position count : UInt64) : Bool :=
  Core.Collections.BoundedSet.forgedPosition position count

/-- Membership decision over the observed scalars: the position addresses a live element and
the backing value equals the key. This is the shared gate for contains views and for trusting
the position before a mutation. -/
@[pf_inline] def isPresent (position count stored key : UInt64) : Bool :=
  Core.Collections.BoundedSet.isPresentAt position count stored key

/-! ### Insert

Insert writes backing slot `insertIndex count = count` (requires `count < capacity`),
stores `map[key] = insertPosition count = count + 1`, and stores the new live count
`insertedCount count = count + 1` — in that order, as one ordered State update plus one map
put. No partial update on failure: duplicate, full, and malformed evidence preflight before any
write. -/

/-- Backing slot that receives an insert. -/
@[pf_inline] def insertIndex (count : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.insertIndex count

/-- Map value stored for the inserted key: backing index + 1 (never the absent `0`). -/
@[pf_inline] def insertPosition (count : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.insertPosition count

/-- Live count stored on successful insert. -/
@[pf_inline] def insertedCount (count : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.insertedCount count

/-- Insert decision against already-observed map evidence: canonical space plus a key the map
reports as absent. -/
@[pf_inline] def canInsert (capacity count position : UInt64) : Bool :=
  Core.Collections.BoundedSet.canInsertAt capacity count position

/-! ### Swap-remove

For a present key at backing index `i = indexOf position = position - 1`, removal reads the
last live element `values[lastIndex count]`. Removing key 0 and removing the last (or only)
element are the `movesLast = false` path: no backing move, only `map[key] = 0` and
`count - 1`. Middle removal swaps the last element into slot `i` and repairs the moved key's
map entry to `i + 1 = position`. Stale backing values become unreachable. -/

/-- Backing index a present position addresses. -/
@[pf_inline] def indexOf (position : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.indexOfPosition position

/-- Backing index of the last live element. -/
@[pf_inline] def lastIndex (count : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.lastIndex count

/-- Swap decision: the removed key's slot differs from the last live slot, so the last element
moves. For the last (or only) element this is exactly `false`. -/
@[pf_inline] def movesLast (position count : UInt64) : Bool :=
  Core.Collections.BoundedSet.movesLast position count

/-- Map value stored for the moved last key (it now sits at the removed key's slot). -/
@[pf_inline] def movedPosition (position : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.movedPosition position

/-- Live count stored on successful remove. -/
@[pf_inline] def removedCount (count : UInt64) : UInt64 :=
  Core.Collections.BoundedSet.removedCount count

/-- Remove decision against already-observed map evidence: canonical nonzero count plus
evidence that the position addresses a live element. Absence is the explicit `absent`
outcome (no store), not this decision. -/
@[pf_inline] def canRemove (capacity count position : UInt64) : Bool :=
  Core.Collections.BoundedSet.canRemoveAt capacity count position

/-! ### Bounded enumeration

Only `canValueAt`-gated index/value reads over the active prefix `0..<live>` are exposed: one
slot read each, O(1), exactly the live set. There is no loop, no `keysAt` bulk read, and no
clear — see the resource contract above. -/

/-- Enumeration read decision: canonical count and an index that addresses the live prefix. -/
@[pf_inline] def canValueAt (capacity count index : UInt64) : Bool :=
  Core.Collections.BoundedSet.canValueAt capacity count index

/-- The `0` fallback views return for out-of-range indexes and malformed counts (mirrors
`Core.Value.BoundedVec`'s out-of-bounds `default`). -/
@[pf_inline] def emptyValue : UInt64 := 0

end ProofForge.Evm.Sdk.StorageEnumerableSet
