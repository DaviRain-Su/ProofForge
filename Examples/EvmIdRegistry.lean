import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableSet

/-!
Enumerable-set consumer B: a permissionless unique-id registry over the
`Evm.Sdk.StorageEnumerableSet` persistent bounded set policy (capacity 3).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageEnumerableSet.Descriptor` bundle is compile-time data erased before extraction (the
hashed `positions` namespace lives in the consumer's `Storage.Layout` cursor and takes base
`1` here, disjoint from the static slot numbering). Every entry reads and writes state through
ordinary typed `State` field/`Vector` accesses: the SDK owns the count/position/evidence
decisions (`wellFormed`/`isFull`/`canValueAt`/`absent`/`forged`/`isPresent`/
`insertPosition`/`removedCount`), each physical write is a visible literal `State`
field/`Vector` update, and the explicit `positions.put` calls form the effect-result carrier.

To stay inside the proven EVM extraction shapes this file follows the same discipline as
`Examples.EvmVecLog` and the probe-verified compositions: hashed-map evidence is an inlined
`positions.get id` comparison (never a `let`-bound carrier or a raw-get result arm), every
dynamic `Vector` read/write sits under an explicit compile-time bounds guard, and every
rejected outcome returns before any store. Swap-remove uses the SDK's `movesLast` policy:
middle removal moves and repairs the last key, while last/only removal avoids both redundant
writes. `Tests/EvmStorageEnumerableSetSpec` proves the extracted slots and the `ids` vector
entry equal the declared layout, and
`runtime-tests/evm/anvil_id_registry.sh` covers the permissionless enroll/release matrix —
swap-remove of the first/middle/last/only element, key `0`, duplicate/full/absent, enumeration
after repair, and fail-closed malformed metadata.

Policy differences from `Examples.EvmAllowlist`: no owner at all, a full set reverts with its
own typed `full()` error (not the shared `CapExceeded()`), and the membership view is the plain
non-reverting `0`/`1` fallback (releasing an id still fails closed on forged metadata).
-/

namespace Examples.EvmIdRegistry

open ProofForge.Evm.Sdk

/-- Compile-time capacity of the registry's backing prefix. -/
abbrev capacity : Nat := 3

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `3`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `EvmVecLog`, `EvmRingHistory`). -/
@[pf_inline] def capU64 : UInt64 := 3

structure State where
  /-- Fixed backing prefix of the bounded registry; only the live `0..<count>` slots are
  reachable. -/
  ids : Vector UInt64 3
  /-- Live id count (`0..3`). -/
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State` (the hashed namespace is separate). -/
structure Handles where
  registry : StorageEnumerableSet.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`; the live map takes
hashed namespace base `1` from the consumer's own `Storage.Layout` cursor. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let registry := StorageEnumerableSet.declare Storage.Static.Layout.root "ids" "count"
    (Storage.Layout.root.u64Map.next.u64Map.handle) capacity
  { handle := { registry := registry.handle }, next := registry.next }

/-- The accumulated static layout: slots `0..3` (`ids_<i>:8@0..2`, `count:8@3`). Hashed-map
namespaces are numbered separately from static slots. -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

/-- The hashed key → position+1 namespace of this registry (base `1`, distinct from the
allowlist consumer's base `0`). -/
@[pf_inline] def positions : Storage.U64Map :=
  Storage.Layout.root.u64Map.next.u64Map.handle

inductive Error where
  | duplicate
  | full
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Constructor is seeded like `EvmRingHistory`: the backing table starts all-zero. -/
@[pf_entry]
def init (_seed : UInt64) : State :=
  { ids := #v[0, 0, 0], count := 0 }

@[pf_entry]
def sizeOf (s : State) : UInt64 :=
  s.count

/-- Enumeration view: the live id at `index`, or the `0` fallback when the index is out of the
live range or the persisted count is malformed (`EvmVecLog.entryAt` shape). -/
@[pf_entry]
def idAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableSet.canValueAt capU64 s.count index then s.ids[index.toNat]! else 0

/-- Membership view: `1` when `id` is live and the persisted metadata is canonical, `0` when it
is absent, the metadata is forged, or the backing leaf mismatches the key (this view never
reverts; it reads forged metadata as plain absence). Id `0` works like any other id: a live
key `0` maps to position `1..count`, never to the absent literal `0`. -/
@[pf_entry]
def containsOf (s : State) (id : UInt64) : UInt64 :=
  if !StorageEnumerableSet.wellFormed capU64 s.count then 0
  else if StorageEnumerableSet.absent (positions.get id) then 0
  else if StorageEnumerableSet.forged (positions.get id) s.count then 0
  else
    if StorageEnumerableSet.isPresent (positions.get id) s.count
        s.ids[(positions.get id - 1).toNat]! id then 1 else 0

/-- Permissionless enroll of one unique id. Malformed count or forged map evidence reverts with
the typed terminal before any store; a replay of a live id reverts with `duplicate()`; a full
registry reverts with `full()`. On success the committed transition is the backing write
`ids[count] = id`, the map put `positions[id] = count + 1`, and the count bump `count + 1` as
one atomic EVM transaction slice; the physical store order inside that transition is an
extraction detail, not part of this contract. -/
@[pf_entry]
def enroll (s : State) (id : UInt64) : Except Error (State × Bool) :=
  if !StorageEnumerableSet.wellFormed capU64 s.count then
    .error .malformed
  else
    if StorageEnumerableSet.absent (positions.get id) then
      if StorageEnumerableSet.isFull capU64 s.count then
        .error .full
      else if h : s.count.toNat < 3 then
        .ok ({ s with ids := s.ids.set s.count.toNat id h, count := s.count + 1 },
          Effect.thenTrue (positions.put id (StorageEnumerableSet.insertPosition s.count)))
      else
        .error .malformed
    else if StorageEnumerableSet.forged (positions.get id) s.count then
      .error .malformed
    else
      if StorageEnumerableSet.isPresent (positions.get id) s.count
          s.ids[(positions.get id - 1).toNat]! id then
        .error .duplicate
      else
        .error .malformed

/-- Permissionless swap-remove. Malformed count or forged/mismatched metadata reverts with the
typed terminal before any store; releasing an absent id is the explicit no-write
`.ok (s, false)` outcome. For a middle id at position `p`, the last live element overwrites
slot `p - 1`, its map entry is repaired to `p`, then `map[id]` clears and count drops. For the
last (or only) id, `movesLast` selects only the clear and count decrement, avoiding a backing
self-write and redundant map repair. Releasing id `0` and releasing to empty both work. -/
@[pf_entry]
def release (s : State) (id : UInt64) : Except Error (State × Bool) :=
  if !StorageEnumerableSet.wellFormed capU64 s.count then
    .error .malformed
  else
    if StorageEnumerableSet.absent (positions.get id) then
      .ok (s, false)
    else if StorageEnumerableSet.forged (positions.get id) s.count then
      .error .malformed
    else
      if StorageEnumerableSet.isPresent (positions.get id) s.count
          s.ids[(positions.get id - 1).toNat]! id then
        if h : (positions.get id - 1).toNat < 3 then
          if StorageEnumerableSet.movesLast (positions.get id) s.count then
            if h2 : (s.count - 1).toNat < 3 then
              .ok ({ s with
                       ids := s.ids.set ((positions.get id - 1).toNat)
                         (s.ids[(s.count - 1).toNat]) h,
                       count := StorageEnumerableSet.removedCount s.count },
                Effect.thenTrue
                  (positions.put (s.ids[(s.count - 1).toNat]) (positions.get id)
                    ||| positions.put id 0))
            else
              .error .malformed
          else
            .ok ({ s with count := StorageEnumerableSet.removedCount s.count },
              Effect.thenTrue (positions.put id 0))
        else
          .error .malformed
      else
        .error .malformed

end Examples.EvmIdRegistry
