import ProofForge.Attr
import ProofForge.Core.Collections
import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.StorageRing

/-!
# EVM SDK persistent bounded storage ring queue of UInt64 (circular buffer)

`StorageRing` is the reusable *persistent* fixed-capacity circular-buffer policy for EVM static
storage (an ordinary Solidity-style head/length/payload triple, like OpenZeppelin's `Queue`
semantics). It binds the shared `Core.Collections.BoundedQueue` fixed-frame FIFO semantics to
the existing physical state model — exactly the way `StorageVec` binds `Core.Value.BoundedVec`
and `StorageBitmap` binds `Core.Collections.BoundedBitSet`:

- **compile-time capacity**: the backing store is an ordinary `Vector UInt64 capacity` field of
  the consumer's `State` structure, flattened by the existing fixed-vector extraction path into
  `capacity` consecutive static slots (`values_0 … values_<capacity-1>`). There is no runtime
  slot allocator, no hashed namespace, and no pointer; the slot table is fixed at extraction.
- **disjoint metadata slots**: one slot holds the physical index of the front element (`head`)
  and one disjoint slot holds the live element count (`length`). They are separate scalar
  fields declared *after* the backing slots, so head, length, and payload never alias.
- **checked ring semantics**: the pure `pf_inline` decisions below own all
  head/length/slot/index policy (`wellFormed`/`isEmpty`/`isFull`/`canPeek`/`canGet`/
  `canPop`/`canPush`/`canClear`); inactive backing slots are never reachable through an
  admissible decision. Wraparound is `mod`-ulo the fixed positive capacity: `absIndex head
  offset capacity = (head + offset) % capacity`, the same arithmetic as
  `Core.Collections.BoundedQueue` (`capacity < UInt32.size`, so host `UInt64` and EVM `mod`
  agree exactly on every reachable value).

## Why decisions, not returned queues

The current EVM extraction lowers dynamic-index `Vector` reads/writes only when the vector is a
`State` field and the index proof is an explicit `if h : … < capacity` hypothesis in the consumer
(`Examples.EvmStaticRoster.setSeat`, `Examples.EvmVecLog.record`). A generic helper returning an
updated queue value is not an extractable shape today, so — exactly like `StorageVec` and
`Roles.Set2` — this module owns the reusable *decisions and slot arithmetic* while applications
own the literal `State` field writes:

```lean
if StorageRing.canPush capacity s.head s.live then
  let tail := StorageRing.absIndex s.head s.live capacity
  if h : tail.toNat < capacity then       -- compiler proof for the physical write
    let next := s.live + 1
    .ok ({ s with values := s.values.set tail.toNat value h, live := next }, …)
  else
    .error .malformed                     -- unreachable under an admissible decision
else
  .ok (s, Revert.capExceeded)
```

The inner `else` is unreachable whenever the SDK decision drives the branch; mapping it to the
application's malformed terminal keeps the write path honest without duplicating policy.

## Physical-state contract

- `values`: a fixed payload table of `capacity` slots; inactive slots are unreachable and may
  retain stale values.
- `head`: the physical slot index (`0.<capacity-1>`) of the front element. While the queue is
  empty, head is the canonical `0` — the same normalization `Core.Collections.BoundedQueue.pop?`
  and `clear` perform — so an emptied queue never carries a masked non-canonical head.
- `live`: the live element count `0..capacity`, always `≤ capacity`.

One word on the semantic binding: `Core.Collections.BoundedQueue.wellFormed` makes the
canonical-empty case (`head = 0` while `length = 0`) part of its invariant and this SDK enforces
exactly that, so host truth tables over `BoundedQueue` are the real policy semantics and every
emitted `mod`/`add`/`sub` is truthful on extraction.

## Fail-closed policy

| situation | decision result | suggested consumer terminal |
|---|---|---|
| `capacity <= head` (malformed head) | every decision is `false` | typed malformed error before any store |
| `head ≠ 0` while `live = 0` (non-canonical empty) | every decision is `false` | typed malformed error before any store |
| `capacity < live` (malformed live count) | every decision is `false` | typed malformed error before any store |
| enqueue when `live = capacity` (full) | `canPush = false` | `CapExceeded()` |
| dequeue/peek when `live = 0` (empty) | `canPop`/`canPeek = false` | typed error / revert before any store |
| get with `live ≤ offset` (OOB) | `canGet = false` | view fallback or typed error |
| clear with canonical state | `canClear = true` | resets only `head`/`live` |
| any mutation with malformed state | decision is `false` | typed malformed error before any store |

`clear` deliberately does not rewrite backing slots: they stay stale and unreachable, matching
`Core.Collections.BoundedQueue.clear`. Zeroing them is an application gas decision, not a
correctness requirement.

## Preflight / no-partial-update ordering

Every mutation is a *decision first, physical writes second*: `canPeek`/`canPop`/`canPush`/
`canClear` is evaluated over the loaded `head`/`live` scalars before any segment of the
consumer's update is bound, and a rejected (or malformed) decision returns without touching any
slot. Under ProofForge's ordered storage semantics a rejected operation therefore stores
neither metadata nor payload — there is no partial head/length/payload update.

## Resource contract (worst case, O(1) in every dimension)

Each operation touches a constant number of *distinct* storage slots, independent of
`capacity`; there is no loop over the backing array. Distinct-slot footprint:

| operation | distinct slots read | slots written | notes |
|---|---|---|---|
| `canGet` read (view) | 3 | 0 | `head`/`live` + selected element slot |
| enqueue | 2 | 2 | gate reads `head`/`live`; stores `values[absIndex head live]` + `live` |
| dequeue | 3 | 2 | reads `head`/`live` + `values[head]`; stores `head` + `live` |
| peek (view) | 3 | 0 | reads `head`/`live` + `values[head]` |
| clear | 2 | 2 | validates, then stores `head` and `live` only |

Two honest qualifiers: (1) the ring slot expressions (`absIndex`, `poppedHead`) are recomputed
at each use site instead of cached in a Yul local — a constant number of `add`/`mod` ops, and
the solc optimizer may CSE them; (2) a consumer's own authorization gate adds its own footprint
(e.g. `Access.requireOwner` reads the three Address limbs of the stored owner). Cold
zero→nonzero SSTORE pricing dominates real gas; the SDK guarantees only the *shape* — constant,
capacity-independent slot count, no iteration. The descriptor is compile-time data erased
before extraction and costs nothing at runtime.
-/

/-- Compile-time descriptor of one persistent bounded UInt64 ring queue: the fixed backing
`Vector UInt64 capacity` field plus the two disjoint runtime-metadata scalars (`head`, `live`,
adjacent directly after the backing slots). Handles are extraction-time data erased before
runtime; they never appear in emitted code. -/
structure Descriptor (capacity : Nat) where
  /-- Fixed backing field: flattens to `capacity` consecutive 8-byte slots. -/
  values : Storage.Static.Handle (Vector UInt64 capacity)
  /-- Physical front index: one 8-byte scalar slot directly after the backing slots. -/
  head : Storage.Static.Handle UInt64
  /-- Live element count: one 8-byte scalar slot directly after the head slot. -/
  live : Storage.Static.Handle UInt64
  deriving Repr

attribute [pf_inline] Descriptor.values Descriptor.head Descriptor.live

/-- Declare the backing vector and its `head`/`live` scalars as consecutive static fields, in
the exact order the consumer's `State` structure declares them (`values` first, `head`
immediately after, `live` immediately after that). -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (valuesName headName liveName : String)
    (capacity : Nat) : Storage.Static.Allocated (Descriptor capacity) :=
  let values := layout.array (α := Vector UInt64 capacity) valuesName .u64 capacity
  let head := values.next.uint64 headName
  let live := head.next.uint64 liveName
  { handle := { values := values.handle, head := head.handle, live := live.handle }
    next := live.next }

/-- Descriptor-level validity, checked by focused tests before any extraction is trusted:
positive codec-representable capacity (so the `mod` wraparound divisor is never zero and the
scalar decomposition cannot overflow), exactly the declared one-slot-per-element UInt64 array
handle, the head scalar occupying the slot directly after the last backing slot, and the live
scalar the slot after that. Zero capacity and geometry overflow fail closed here, before any
extraction is trusted. -/
def Descriptor.wellFormed {capacity : Nat} (queue : Descriptor capacity) : Bool :=
  0 < capacity && capacity < UInt32.size &&
    queue.values.wellFormed && queue.head.wellFormed && queue.live.wellFormed &&
    queue.values.spec == Storage.Static.Spec.arrayLeaves .u64 capacity &&
    queue.head.spec == Storage.Static.Spec.leaf .u64 &&
    queue.live.spec == Storage.Static.Spec.leaf .u64 &&
    queue.head.slot? == some (queue.values.baseSlot + capacity) &&
    queue.live.slot? == some (queue.values.baseSlot + capacity + 1)

/-! ## Runtime policy decisions

All decisions are pure `pf_inline` functions over the explicit `head`/`live` scalars and the
compile-time `capacity` scalar. `capacity` must decode to a compile-time literal at every call
site (consumers expose one `@[pf_inline]` capacity literal for it); only
`head`/`live`/`offset` are runtime values. Every decision rechecks `wellFormed`, so malformed
persisted head/length fails closed even if storage was corrupted outside the component. -/

/-- Persisted metadata is canonical: `head < capacity`, `live ≤ capacity`, and an empty queue
carries the canonical head `0`. Any corrupted over-capacity head/live pair fails closed. -/
@[pf_inline] def wellFormed (capacity head live : UInt64) : Bool :=
  0 < capacity && live ≤ capacity && (if live == 0 then head == 0 else head < capacity)

/-- No live elements. -/
@[pf_inline] def isEmpty (live : UInt64) : Bool :=
  live == 0

/-- The live elements already occupy every backing slot. -/
@[pf_inline] def isFull (capacity live : UInt64) : Bool :=
  capacity ≤ live

/-- Physical slot of one live offset from the front: `(head + offset) % capacity`, the same
wraparound modulo the fixed positive capacity as `Core.Collections.BoundedQueue`. Meaningful
only under an admissible decision (`wellFormed` + a live offset). -/
@[pf_inline] def absIndex (head offset capacity : UInt64) : UInt64 :=
  (head + offset) % capacity

/-- Enqueue decision: canonical empty space at the tail (`live < capacity`). The enqueue writes
backing slot `absIndex head live capacity` and stores `live + 1`; head is unchanged. -/
@[pf_inline] def canPush (capacity head live : UInt64) : Bool :=
  wellFormed capacity head live && !isFull capacity live

/-- Dequeue decision: canonical nonzero live count. The dequeue reads backing slot `head`,
stores `poppedHead head live capacity` and `live - 1`; the popped slot keeps its stale value
and stays unreachable. -/
@[pf_inline] def canPop (capacity head live : UInt64) : Bool :=
  wellFormed capacity head live && !isEmpty live

/-- Front read decision: the same admissible state as a dequeue, without mutating. -/
@[pf_inline] def canPeek (capacity head live : UInt64) : Bool :=
  wellFormed capacity head live && !isEmpty live

/-- Runtime-indexed read decision: `offset` addresses a live element counted from the front;
`absIndex head offset capacity` is its physical slot. -/
@[pf_inline] def canGet (capacity head live offset : UInt64) : Bool :=
  wellFormed capacity head live && offset < live

/-- Head stored by a dequeue: the successor of the front inside the ring, canonical `0` when
the queue empties (`live == 1`), matching `Core.Collections.BoundedQueue.pop?`. Meaningful
when `canPop`. -/
@[pf_inline] def poppedHead (head live capacity : UInt64) : UInt64 :=
  if live == 1 then 0 else absIndex head 1 capacity

/-- Clear decision: only canonical storage may transition. A corrupted over-capacity head/live
pair is not silently repaired because every persistent mutation must fail closed on malformed
state. -/
@[pf_inline] def canClear (capacity head live : UInt64) : Bool :=
  wellFormed capacity head live

/-- Head stored by a clear. Backing slots keep their stale values and become unreachable. -/
@[pf_inline] def clearedHead : UInt64 := 0

/-- Live count stored by a clear. Backing slots keep their stale values and become unreachable. -/
@[pf_inline] def clearedLive : UInt64 := 0

end ProofForge.Evm.Sdk.StorageRing
