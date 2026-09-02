import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# ProofForge bounded direct-write NEAR Queue storage

`DirectQueue64` is a ProofForge-owned persistent `UInt64` FIFO ring. Current near-sdk-rs
`store::*` exports no Queue, so this type claims no Rust SDK collection compatibility. Its durable
element slots deliberately reuse the current direct Vector recipe:

* key: `prefix || u32_le(physicalIndex)`;
* value: standalone eight-byte little-endian Borsh `UInt64`;
* capacity: a compile-time bound in `1..64`.

The caller owns `head` and `length` as ordinary ProofForge state until the NEAR `STATE` lifecycle
lands. The canonical empty state is `head = length = 0`. Every read predicate validates metadata
before constructing a key, and callers must establish `canPush` before using `physicalIndex head
length` as the tail. Pop consumers remove the front key and update metadata in the same successful
entry; nearcore rollback keeps immediate slot effects atomic with ordinary state updates.

Prefixes remain caller-owned namespaces and must be disjoint from every map, set, vector, raw,
queue, and compiler state-field key. Generic values, iteration, resizing, persistent metadata,
hidden flushes, and legacy near-sdk collection layouts are outside this bounded slice.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time FIFO ring capacity. The current bounded collection profile accepts `1..64`. -/
abbrev DirectQueue64 := Nat

def DirectQueue64.wellFormed (queue : DirectQueue64) : Bool :=
  Codec.storageCapacityValid queue

@[pf_inline] def DirectQueue64.bounded (capacity : Nat) : DirectQueue64 :=
  capacity

/-- Validate caller-owned ring metadata. Empty queues have one canonical head; non-empty queues
must point inside the fixed ring. -/
@[pf_inline] def DirectQueue64.validState
    (queue : DirectQueue64) (head length : UInt64) : Bool :=
  let capacity := UInt64.ofNat queue
  if capacity = 0 then false
  else if capacity ≤ 64 then
    if length ≤ capacity then
      if length = 0 then head = 0 else head < capacity
    else false
  else false

@[pf_inline] def DirectQueue64.canPush
    (queue : DirectQueue64) (head length : UInt64) : Bool :=
  if queue.validState head length then length < UInt64.ofNat queue else false

@[pf_inline] def DirectQueue64.canPop
    (queue : DirectQueue64) (head length : UInt64) : Bool :=
  if queue.validState head length then length != 0 else false

/-- Whether a zero-based logical offset from the front is active. -/
@[pf_inline] def DirectQueue64.offsetInRange
    (queue : DirectQueue64) (head length offset : UInt64) : Bool :=
  if queue.validState head length then offset < length else false

/-- Convert a validated ring offset to a physical zero-based slot with at most one wrap. Callers
must establish `head < capacity` and `offset < capacity`; `canPush` establishes this for the tail
offset `length`, while `offsetInRange` establishes it for reads. -/
@[pf_inline] def DirectQueue64.physicalIndex
    (queue : DirectQueue64) (head offset : UInt64) : UInt64 :=
  let raw := head + offset
  if raw < UInt64.ofNat queue then raw else raw - UInt64.ofNat queue

/-- Ring successor for a validated non-empty head. -/
@[pf_inline] def DirectQueue64.nextHead
    (queue : DirectQueue64) (head : UInt64) : UInt64 :=
  if head + 1 < UInt64.ofNat queue then head + 1 else 0

@[pf_inline] def DirectQueue64.elementKey
    (_queue : DirectQueue64) (tag : Prefix4) (index : UInt64) : BoundedBytes 8 :=
  tag.keyUInt32 index

@[pf_inline] def DirectQueue64.elementValue
    (_queue : DirectQueue64) (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

@[pf_inline] def DirectQueue64.resultValueD
    (_queue : DirectQueue64) (fallback : UInt64) : UInt64 :=
  resultUInt64D fallback

/-- Return raw NEAR presence status for one active logical offset. Malformed metadata and inactive
offsets fail closed without issuing a host call. -/
@[pf_inline] def DirectQueue64.hasOffset
    (queue : DirectQueue64) (tag : Prefix4) (head length offset : UInt64) : UInt64 :=
  if queue.offsetInRange head length offset then
    let index := queue.physicalIndex head offset
    let result : ResultBuffer := 8
    let _ := result.hasKey (queue.elementKey tag index)
    result.status
  else 0

/-- Read and decode one active logical offset. Missing/malformed values use `fallback`; callers
that need to distinguish an absent slot from a stored fallback value first call `hasOffset`. -/
@[pf_inline] def DirectQueue64.getD
    (queue : DirectQueue64) (tag : Prefix4)
    (head length offset fallback : UInt64) : UInt64 :=
  if queue.offsetInRange head length offset then
    let index := queue.physicalIndex head offset
    let result : ResultBuffer := 8
    let _ := result.read (queue.elementKey tag index)
    queue.resultValueD fallback
  else fallback

/-- Source-level queue handle: compile-time capacity + `Prefix4`. `head`/`length` stay in STATE
(N9); this type never persists metadata or invents a second length key. Methods are thin
`@[pf_inline]` facades over `DirectQueue64` so Extract sees the same shapes as raw calls. -/
structure DirectQueue64.Handle where
  capacity : DirectQueue64
  tag : Prefix4
  deriving Repr

@[pf_inline] def DirectQueue64.handle (capacity : Nat) (tag : Prefix4) : DirectQueue64.Handle :=
  { capacity := capacity, tag := tag }

@[pf_inline] def DirectQueue64.Handle.validState
    (h : DirectQueue64.Handle) (head length : UInt64) : Bool :=
  DirectQueue64.validState h.capacity head length

@[pf_inline] def DirectQueue64.Handle.canPush
    (h : DirectQueue64.Handle) (head length : UInt64) : Bool :=
  DirectQueue64.canPush h.capacity head length

@[pf_inline] def DirectQueue64.Handle.canPop
    (h : DirectQueue64.Handle) (head length : UInt64) : Bool :=
  DirectQueue64.canPop h.capacity head length

@[pf_inline] def DirectQueue64.Handle.offsetInRange
    (h : DirectQueue64.Handle) (head length offset : UInt64) : Bool :=
  DirectQueue64.offsetInRange h.capacity head length offset

@[pf_inline] def DirectQueue64.Handle.physicalIndex
    (h : DirectQueue64.Handle) (head offset : UInt64) : UInt64 :=
  DirectQueue64.physicalIndex h.capacity head offset

@[pf_inline] def DirectQueue64.Handle.nextHead
    (h : DirectQueue64.Handle) (head : UInt64) : UInt64 :=
  DirectQueue64.nextHead h.capacity head

@[pf_inline] def DirectQueue64.Handle.elementKey
    (h : DirectQueue64.Handle) (index : UInt64) : BoundedBytes 8 :=
  DirectQueue64.elementKey h.capacity h.tag index

@[pf_inline] def DirectQueue64.Handle.elementValue
    (h : DirectQueue64.Handle) (value : UInt64) : BoundedBytes 8 :=
  DirectQueue64.elementValue h.capacity value

@[pf_inline] def DirectQueue64.Handle.hasOffset
    (h : DirectQueue64.Handle) (head length offset : UInt64) : UInt64 :=
  DirectQueue64.hasOffset h.capacity h.tag head length offset

@[pf_inline] def DirectQueue64.Handle.getD
    (h : DirectQueue64.Handle) (head length offset fallback : UInt64) : UInt64 :=
  DirectQueue64.getD h.capacity h.tag head length offset fallback

end ProofForge.Wasm.Near.Sdk.Store
