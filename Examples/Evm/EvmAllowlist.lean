import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableSet

/-!
Enumerable-set consumer A: an owner-gated membership allowlist over the
`Evm.Sdk.StorageEnumerableSet` persistent bounded set policy (capacity 4).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageEnumerableSet.Descriptor` bundle is compile-time data erased before extraction (the
hashed `positions` namespace lives in the consumer's `Storage.Layout` cursor, a separate
numbering). Every entry reads and writes state through ordinary typed `State` field/`Vector`
accesses: the SDK owns the count/position/evidence decisions
(`wellFormed`/`isFull`/`canValueAt`/`absent`/`forged`/`isPresent`/`insertPosition`/
`removedCount`), each physical write is a visible literal `State` field/`Vector` update, and
the explicit `positions.put` calls form the effect-result carrier. This file follows the
probe-verified extraction discipline documented in `Examples.Evm.EvmIdRegistry` (inlined hashed-map
evidence comparisons, compile-time dite guards around dynamic `Vector` access, failed outcomes
before any store). `Tests/EvmStorageEnumerableSetSpec` proves the extracted slots and the
`members` vector entry equal the declared layout, and
`runtime-tests/evm/anvil_allowlist.sh` covers the owner-gated insert/remove/swap-repair matrix
plus unauthorized and malformed probes.

Policy differences from `Examples.Evm.EvmIdRegistry`: this allowlist is owner-gated on both
mutations, rejects a full set with the shared `CapExceeded()` revert carrier on a `.ok`
success shape (instead of a typed `full()` error), and its membership view reverts with the
typed `malformed()` terminal on forged metadata instead of reading it as absence.
-/

namespace Examples.Evm.EvmAllowlist
open ProofForge.Evm.Sdk

/-- Compile-time capacity of the allowlist's backing prefix. -/
abbrev capacity : Nat := 4

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `4`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `EvmVecLog`, `EvmRingHistory`). -/
@[pf_inline] def capU64 : UInt64 := 4

structure State where
  admin : Address
  /-- Fixed backing prefix of the bounded allowlist; only the live `0..<count>` slots are
  reachable. -/
  members : Vector UInt64 4
  /-- Live member count (`0..4`). -/
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State` (the hashed namespace is separate). -/
structure Handles where
  admin : Storage.Static.Handle Address
  set : StorageEnumerableSet.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`; the live map takes
hashed namespace base `0` from the consumer's own `Storage.Layout` cursor. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let set := StorageEnumerableSet.declare admin.next "members" "count"
    (Storage.Layout.root.u64Map.handle) capacity
  { handle := { admin := admin.handle, set := set.handle }, next := set.next }

/-- The accumulated static layout: slots `0..7` (`admin_w0..w2:8@0..2`, `members_<i>:8@3..6`,
`count:8@7`). Hashed-map namespaces are numbered separately from static slots. -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

/-- The hashed key → position+1 namespace of this allowlist (base `0`). -/
@[pf_inline] def positions : Storage.U64Map := Storage.Layout.root.u64Map.handle

inductive Error where
  | duplicate
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, members := #v[0, 0, 0, 0], count := 0 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def sizeOf (s : State) : UInt64 :=
  s.count

/-- Enumeration view: the live member at `index`, or the `0` fallback when the index is out of
the live range or the persisted count is malformed (`EvmVecLog.entryAt` shape). -/
@[pf_entry]
def memberAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableSet.canValueAt capU64 s.count index then s.members[index.toNat]! else 0

/-- Membership view: `1` when `key` is a live member and the persisted metadata is canonical,
`0` when the key is absent, and a typed `malformed()` revert when the map metadata is forged
or the backing leaf mismatches the key. Key `0` works like any other key. -/
@[pf_entry]
def containsOf (s : State) (key : UInt64) : Except Error (State × UInt64) :=
  if !StorageEnumerableSet.wellFormed capU64 s.count then
    .error .malformed
  else
    if StorageEnumerableSet.absent (positions.get key) then
      .ok (s, 0)
    else if StorageEnumerableSet.forged (positions.get key) s.count then
      .error .malformed
    else
      if StorageEnumerableSet.isPresent (positions.get key) s.count
          s.members[(positions.get key - 1).toNat]! key then
        .ok (s, 1)
      else
        .error .malformed

/-- Owner-gated insert. Malformed count or forged map evidence reverts with the typed terminal
before any store; a replay of a live member reverts with `duplicate()`; a full set takes the
shared `CapExceeded()` revert carrier. On success the committed transition is the backing
write `members[count] = key`, the map put `positions[key] = count + 1`, and the count bump as
one atomic EVM transaction slice; the physical store order inside that transition is an
extraction detail, not part of this contract. -/
@[pf_entry]
def grant (s : State) (key : UInt64) : Except Error (State × Bool) :=
  if Access.requireOwner s.admin then
    if !StorageEnumerableSet.wellFormed capU64 s.count then
      .error .malformed
    else
      if StorageEnumerableSet.absent (positions.get key) then
        if StorageEnumerableSet.isFull capU64 s.count then
          .ok (s, Effect.thenTrue Revert.capExceeded)
        else if h : s.count.toNat < 4 then
          .ok ({ s with members := s.members.set s.count.toNat key h,
                        count := s.count + 1 },
            Effect.thenTrue (positions.put key (StorageEnumerableSet.insertPosition s.count)))
        else
          .error .malformed
      else if StorageEnumerableSet.forged (positions.get key) s.count then
        .error .malformed
      else
        if StorageEnumerableSet.isPresent (positions.get key) s.count
            s.members[(positions.get key - 1).toNat]! key then
          .error .duplicate
        else
          .error .malformed
  else
    .ok (s, Effect.thenTrue Access.ownerViolation)

/-- Owner-gated swap-remove (the `EvmIdRegistry.release` shape, plus the ownership gate).
Malformed count or forged/mismatched metadata reverts with the typed terminal before any store;
removing an absent key is the explicit no-write `.ok (s, false)` outcome. For a middle key at
position `p` (slot `i = p - 1`), the last live element overwrites slot `i`, the moved key's map
entry is repaired to `p`, then `map[key]` clears to `0` and `count` drops by one. For the last
(or only) key, `movesLast` selects the smaller transition: no backing self-write and no redundant
moved-key repair, only the clear and count decrement. Removing key `0` and removing to empty both
work. -/
@[pf_entry]
def revoke (s : State) (key : UInt64) : Except Error (State × Bool) :=
  if Access.requireOwner s.admin then
    if !StorageEnumerableSet.wellFormed capU64 s.count then
      .error .malformed
    else
      if StorageEnumerableSet.absent (positions.get key) then
        .ok (s, false)
      else if StorageEnumerableSet.forged (positions.get key) s.count then
        .error .malformed
      else
        if StorageEnumerableSet.isPresent (positions.get key) s.count
            s.members[(positions.get key - 1).toNat]! key then
          if h : (positions.get key - 1).toNat < 4 then
            if StorageEnumerableSet.movesLast (positions.get key) s.count then
              if h2 : (s.count - 1).toNat < 4 then
                .ok ({ s with
                         members := s.members.set ((positions.get key - 1).toNat)
                           (s.members[(s.count - 1).toNat]) h,
                         count := StorageEnumerableSet.removedCount s.count },
                  Effect.thenTrue
                    (positions.put (s.members[(s.count - 1).toNat]) (positions.get key)
                      ||| positions.put key 0))
              else
                .error .malformed
            else
              .ok ({ s with count := StorageEnumerableSet.removedCount s.count },
                Effect.thenTrue (positions.put key 0))
          else
            .error .malformed
        else
          .error .malformed
  else
    .ok (s, Effect.thenTrue Access.ownerViolation)

end Examples.Evm.EvmAllowlist