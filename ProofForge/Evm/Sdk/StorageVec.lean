import ProofForge.Attr
import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.StorageVec

/-!
# EVM SDK persistent bounded storage vector of UInt64 (R5-010)

`StorageVec` is the first reusable *persistent* bounded-vector policy for EVM storage. It binds
the shared `Core.Value.BoundedVec` active-prefix semantics to the existing physical state model:

- **compile-time capacity**: the backing store is an ordinary `Vector UInt64 capacity` field of
  the consumer's `State` structure, flattened by the existing fixed-vector extraction path into
  `capacity` consecutive static slots (`values_0 … values_<capacity-1>`). There is no runtime
  slot allocator, no hashed namespace, and no pointer; the slot table is fixed at extraction.
- **explicit runtime length**: one adjacent `UInt64` scalar field is the active-element count.
  A length above the capacity is *malformed* and every mutation decision fails closed on it.
- **checked active-prefix reads/mutations**: the pure `pf_inline` decisions below own all
  length/index policy (`canPush`/`canPop`/`canGet`/`canSet`/`canClear`); inactive backing slots are
  never reachable through an admissible decision.

## Why decisions, not returned vectors

The current EVM extraction lowers dynamic-index `Vector` reads/writes only when the vector is a
`State` field and the index proof is an explicit `if h : … < capacity` hypothesis in the consumer
(`Examples.Evm.EvmStaticRoster.setSeat`, `Examples.Lang.setAt`). A generic helper returning an updated
`Vector UInt64 capacity` value is not an extractable shape today, so — exactly like
`Roles.Set2` — this module owns the reusable *decisions* while applications own the literal
`State` field writes:

```lean
if StorageVec.canPush capacity s.count then
  if h : s.count.toNat < capacity then        -- compiler proof for the physical write
    .ok ({ s with entries := s.entries.set s.count.toNat value h, count := s.count + 1 }, …)
  else
    .error .malformed                          -- unreachable under an admissible decision
else
  .ok (s, Revert.capExceeded)
```

The inner `else` is unreachable whenever the SDK decision drives the branch; mapping it to the
application's malformed terminal keeps the write path honest without duplicating policy.

## Fail-closed policy

| situation | decision result | suggested consumer terminal |
|---|---|---|
| `capacity < length` (malformed length) | every decision is `false` | typed error / revert before any store |
| push when `length = capacity` (full) | `canPush = false` | `CapExceeded()` |
| pop when `length = 0` (empty) | `canPop = false` | typed error / revert before any store |
| get/set with `length ≤ index` (OOB) | `canGet`/`canSet = false` | view fallback or typed error |
| clear with canonical length | `canClear = true` | resets only the length field |
| any mutation with malformed length | decision is `false` | typed malformed error before any store |

`clear` deliberately does not rewrite backing slots: they stay stale and unreachable, matching
`Core.Value.BoundedVec.clear` and the SVM account-vector pop contract. Zeroing them is an
application gas decision, not a correctness requirement.

## Resource contract (worst case, O(1) in every dimension)

Each operation touches a constant number of *distinct* storage slots, independent of
`capacity`; there is no loop over the backing array. Distinct-slot footprint:

| operation | distinct slots read | slots written | notes |
|---|---|---|---|
| `canGet` read (view) | 2 | 0 | `count` + selected element slot |
| push | 1 | 2 | gate reads `count`; stores `values[length]` and `count` |
| pop | 2 | 1 | reads `count` and `values[length-1]`; stores `count` |
| set | 1 | 1 | gate reads `count`; stores `values[index]` |
| clear | 1 | 1 | validates, then stores `count` only |

Two honest qualifiers: (1) the current emitter re-loads the length scalar at each decision
subexpression instead of caching it in a local, so the Yul contains several SLOADs of the same
slot — the first is cold, the rest are warm, and the solc optimizer may CSE them; (2) a
consumer's own authorization gate adds its own footprint (e.g. `Access.requireOwner` reads the
three Address limbs of the stored owner). Cold zero→nonzero SSTORE pricing dominates real gas;
the SDK guarantees only the *shape* — constant, capacity-independent slot count, no iteration.
The descriptor is compile-time data erased before extraction and costs nothing at runtime.
-/

/-- Compile-time descriptor of one persistent bounded UInt64 vector: the fixed backing
`Vector UInt64 capacity` field plus the adjacent explicit runtime-length scalar. Handles are
extraction-time data erased before runtime; they never appear in emitted code. -/
structure Descriptor (capacity : Nat) where
  /-- Fixed backing field: flattens to `capacity` consecutive 8-byte slots. -/
  values : Storage.Static.Handle (Vector UInt64 capacity)
  /-- Explicit runtime length: one 8-byte scalar slot directly after the backing slots. -/
  count : Storage.Static.Handle UInt64
  deriving Repr

/-- Declare the backing vector and its length scalar as consecutive static fields, in the exact
order the consumer's `State` structure declares them (`values` first, `count` immediately
after). -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (valuesName countName : String)
    (capacity : Nat) : Storage.Static.Allocated (Descriptor capacity) :=
  let values := layout.array (α := Vector UInt64 capacity) valuesName .u64 capacity
  let count := values.next.uint64 countName
  { handle := { values := values.handle, count := count.handle }, next := count.next }

/-- Descriptor-level validity, checked by focused tests before any extraction is trusted:
positive codec-representable capacity, exactly the declared one-slot-per-element UInt64 array
handle of length `capacity`, and the length scalar occupying the slot directly after the last
backing slot. -/
def Descriptor.wellFormed {capacity : Nat} (vec : Descriptor capacity) : Bool :=
  0 < capacity && capacity < UInt32.size &&
    vec.values.wellFormed && vec.count.wellFormed &&
    vec.values.spec == Storage.Static.Spec.arrayLeaves .u64 capacity &&
    vec.count.spec == Storage.Static.Spec.leaf .u64 &&
    vec.count.slot? == some (vec.values.baseSlot + capacity)

/-! ## Runtime policy decisions

All decisions are pure `pf_inline` functions over the explicit `length` scalar and the
compile-time `capacity` scalar. `capacity` must decode to a compile-time literal at every call
site (consumers expose one `@[pf_inline]` capacity literal for it); only
`length`/`index` are runtime values. Every decision rechecks `wellFormed`, so a malformed length
fails closed even if storage was corrupted outside the component. -/

/-- The runtime length is canonical: it never exceeds the compile-time capacity. -/
@[pf_inline] def wellFormed (capacity : UInt64) (length : UInt64) : Bool :=
  length ≤ capacity

/-- No active elements. -/
@[pf_inline] def isEmpty (length : UInt64) : Bool :=
  length == 0

/-- The active prefix already occupies every backing slot. -/
@[pf_inline] def isFull (capacity : UInt64) (length : UInt64) : Bool :=
  capacity ≤ length

/-- Push decision: canonical length strictly below capacity. The push writes backing index
`length.toNat` and stores `length + 1`. -/
@[pf_inline] def canPush (capacity : UInt64) (length : UInt64) : Bool :=
  wellFormed capacity length && !isFull capacity length

/-- Pop decision: canonical nonzero length. The pop reads backing index `length.toNat - 1` and
stores `length - 1`; the popped slot stays stale and unreachable. -/
@[pf_inline] def canPop (capacity : UInt64) (length : UInt64) : Bool :=
  wellFormed capacity length && !isEmpty length

/-- Active-prefix index decision: `index` addresses a live element. This is the shared gate for
checked reads (`canGet`) and overwrites (`canSet`). -/
@[pf_inline] def active (capacity : UInt64) (length index : UInt64) : Bool :=
  wellFormed capacity length && index < length

/-- Checked read decision. -/
@[pf_inline] def canGet (capacity : UInt64) (length index : UInt64) : Bool :=
  active capacity length index

/-- Checked overwrite decision. -/
@[pf_inline] def canSet (capacity : UInt64) (length index : UInt64) : Bool :=
  active capacity length index

/-- Clear decision: only canonical storage may transition. A corrupted over-capacity length is
not silently repaired because every persistent mutation must fail closed on malformed state. -/
@[pf_inline] def canClear (capacity : UInt64) (length : UInt64) : Bool :=
  wellFormed capacity length

/-- Backing index a pop reads and logically removes (`length - 1`); meaningful when `canPop`. -/
@[pf_inline] def popIndex (length : UInt64) : UInt64 :=
  length - 1

/-- Length stored by a clear. Backing slots keep their stale values and become unreachable. -/
@[pf_inline] def clearedLength : UInt64 := 0

end ProofForge.Evm.Sdk.StorageVec
