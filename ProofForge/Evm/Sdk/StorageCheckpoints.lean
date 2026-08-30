import ProofForge.Attr
import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.StorageCheckpoints

/-!
# EVM SDK persistent bounded UInt64 checkpoints (R5-018)

This component is the fixed-resource counterpart of OpenZeppelin `Checkpoints.Trace*`: an
ordered persistent sequence of `(key, value)` pairs, with append-or-latest-overwrite updates,
latest lookup, and lower-bound lookup (the first checkpoint whose key is greater than or equal
to a query).

The physical representation is entirely static: two adjacent `Vector UInt64 capacity` fields
followed by one live-count scalar. There is no dynamic array, hashed map, runtime slot allocator,
pointer, heap object, or new Runtime/Ops/IR/Emit vocabulary. Applications keep literal State
vector writes and compiler-visible bounds proofs; this module owns only reusable descriptor,
ordering, update, and lookup policy.

V1 intentionally admits capacities `1..4`. The extractor's currently qualified fixed-vector
write boundary requires explicit finite arity, so runtime policy receives four key lanes; lanes
above the declared capacity are ignored. This is an honest bounded ceiling rather than a fake
unbounded trace. A later wider implementation can raise the descriptor ceiling together with
its extraction and runtime resource qualification.
-/

/-- Compile-time geometry of one bounded checkpoint trace. Keys, values, and count are adjacent
ordinary static fields and are erased as descriptor data before extraction. -/
structure Descriptor (capacity : Nat) where
  keys : Storage.Static.Handle (Vector UInt64 capacity)
  values : Storage.Static.Handle (Vector UInt64 capacity)
  count : Storage.Static.Handle UInt64
  deriving Repr

/-- Declare keys, values, then count in the same order as the consumer's State fields. -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (keysName valuesName countName : String)
    (capacity : Nat) : Storage.Static.Allocated (Descriptor capacity) :=
  let keys := layout.array (α := Vector UInt64 capacity) keysName .u64 capacity
  let values := keys.next.array (α := Vector UInt64 capacity) valuesName .u64 capacity
  let count := values.next.uint64 countName
  { handle := { keys := keys.handle, values := values.handle, count := count.handle }
    next := count.next }

/-- Descriptor validation pins the V1 resource ceiling and exact non-overlapping static geometry.
Zero or unsupported capacity, a wrong leaf shape, or a displaced values/count field fails closed. -/
def Descriptor.wellFormed {capacity : Nat} (trace : Descriptor capacity) : Bool :=
  0 < capacity && capacity ≤ 4 &&
    trace.keys.wellFormed && trace.values.wellFormed && trace.count.wellFormed &&
    trace.keys.spec == Storage.Static.Spec.arrayLeaves .u64 capacity &&
    trace.values.spec == Storage.Static.Spec.arrayLeaves .u64 capacity &&
    trace.count.spec == Storage.Static.Spec.leaf .u64 &&
    trace.values.baseSlot == trace.keys.baseSlot + capacity &&
    trace.count.slot? == some (trace.keys.baseSlot + capacity + capacity)

/-! ## Runtime policy

The four key arguments are the fixed V1 key frame. For capacities below four, callers pass zero
for unavailable lanes; `count ≤ capacity` makes them semantically unreachable. Every update and
lookup first checks `wellFormed`, including strict ordering of the complete live prefix.
-/

/-- Strictly increasing order over the active prefix of a four-lane key frame. -/
@[pf_inline] def ordered (count key0 key1 key2 key3 : UInt64) : Bool :=
  if count ≤ 1 then true
  else if key0 < key1 then
    if count ≤ 2 then true
    else if key1 < key2 then
      if count ≤ 3 then true else key2 < key3
    else false
  else false

/-- Canonical persistent metadata: supported positive capacity, bounded count, and strictly
increasing live keys. Duplicate or decreasing stored keys are malformed. -/
@[pf_inline] def wellFormed (capacity count key0 key1 key2 key3 : UInt64) : Bool :=
  0 < capacity && capacity ≤ 4 && count ≤ capacity &&
    ordered count key0 key1 key2 key3

/-- No live checkpoints. -/
@[pf_inline] def isEmpty (count : UInt64) : Bool :=
  count == 0

/-- Every statically allocated pair is live. -/
@[pf_inline] def isFull (capacity count : UInt64) : Bool :=
  capacity ≤ count

/-- Index of the latest pair; meaningful only when the trace is nonempty and well formed. -/
@[pf_inline] def latestIndex (count : UInt64) : UInt64 :=
  count - 1

/-- Latest key selected from the fixed frame. Returns zero for an empty trace. -/
@[pf_inline] def latestKey (count key0 key1 key2 key3 : UInt64) : UInt64 :=
  if count == 0 then 0
  else if count == 1 then key0
  else if count == 2 then key1
  else if count == 3 then key2
  else key3

/-- Same-key updates overwrite the latest value without growing the trace. Full traces still
admit this operation. Malformed state fails closed. -/
@[pf_inline] def canOverwrite (capacity count key0 key1 key2 key3 newKey : UInt64) : Bool :=
  wellFormed capacity count key0 key1 key2 key3 && !isEmpty count &&
    latestKey count key0 key1 key2 key3 == newKey

/-- A new key may append only when capacity remains and it is strictly greater than the latest
key (or the trace is empty). Malformed state, duplicate latest keys, decreasing keys, and full
growth fail closed. -/
@[pf_inline] def canAppend (capacity count key0 key1 key2 key3 newKey : UInt64) : Bool :=
  wellFormed capacity count key0 key1 key2 key3 && !isFull capacity count &&
    (isEmpty count || latestKey count key0 key1 key2 key3 < newKey)

/-- A candidate is below the latest live key. This remains a distinct ordered-key rejection even
when the trace is already full; capacity exhaustion applies only to otherwise valid growth. -/
@[pf_inline] def isDecreasing (capacity count key0 key1 key2 key3 newKey : UInt64) : Bool :=
  wellFormed capacity count key0 key1 key2 key3 && !isEmpty count &&
    newKey < latestKey count key0 key1 key2 key3

/-- Count stored after an append. -/
@[pf_inline] def appendedCount (count : UInt64) : UInt64 :=
  count + 1

/-- First live index whose key is at least `query`; `count` is the not-found sentinel. The caller
must reject malformed state before trusting this result. -/
@[pf_inline] def lowerBoundIndex (count query key0 key1 key2 key3 : UInt64) : UInt64 :=
  if 0 < count && query ≤ key0 then 0
  else if 1 < count && query ≤ key1 then 1
  else if 2 < count && query ≤ key2 then 2
  else if 3 < count && query ≤ key3 then 3
  else count

/-- A lower-bound result addresses one live pair rather than the not-found sentinel. -/
@[pf_inline] def hasLowerBound (count index : UInt64) : Bool :=
  index < count

/-- Canonical fallback for empty, not-found, or malformed views. -/
@[pf_inline] def emptyValue : UInt64 := 0

end ProofForge.Evm.Sdk.StorageCheckpoints
