import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableMap

/-!
Owner-managed capacity-4 UInt64 configuration table. This is the first independent consumer of
`Evm.Sdk.StorageEnumerableMap`: fixed key enumeration is ordinary State storage, while two distinct
hashed namespaces own key positions and values. Key zero and value zero are valid; existing-key
writes update only the value namespace, and remove uses the reusable swap-repair policy.
-/

namespace Examples.EvmConfigMap

open ProofForge.Evm.Sdk

abbrev capacity : Nat := 4

@[pf_inline] def capU64 : UInt64 := 4

structure State where
  admin : Address
  keys : Vector UInt64 4
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  admin : Storage.Static.Handle Address
  table : StorageEnumerableMap.Descriptor capacity

@[pf_inline] def positionAllocation := Storage.Layout.root.u64Map
@[pf_inline] def valueAllocation := positionAllocation.next.u64Map

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let table := StorageEnumerableMap.declare admin.next "keys" "count"
    positionAllocation.handle valueAllocation.handle capacity
  { handle := { admin := admin.handle, table := table.handle }, next := table.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next
@[pf_inline] def positions : Storage.U64Map := positionAllocation.handle
@[pf_inline] def values : Storage.U64Map := valueAllocation.handle

inductive Error where
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, keys := #v[0, 0, 0, 0], count := 0 }

@[pf_entry]
def adminOf (s : State) : Address := s.admin

@[pf_entry]
def sizeOf (s : State) : UInt64 := s.count

@[pf_entry]
def keyAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableMap.canEntryAt capU64 s.count index then s.keys[index.toNat]! else 0

/-- Enumerate the value associated with the live key at `index`. -/
@[pf_entry]
def valueAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableMap.canEntryAt capU64 s.count index then
    values.get s.keys[index.toNat]!
  else
    0

/-- Strict key lookup: exact absence returns zero, while forged position/backing evidence is a
typed failure rather than silently exposing a stale hashed value. -/
@[pf_entry]
def valueOf (s : State) (key : UInt64) : Except Error (State × UInt64) :=
  if !StorageEnumerableMap.wellFormed capU64 s.count then
    .error .malformed
  else if StorageEnumerableMap.absent (positions.get key) then
    .ok (s, 0)
  else if StorageEnumerableMap.forged (positions.get key) s.count then
    .error .malformed
  else if StorageEnumerableMap.isPresent (positions.get key) s.count
      s.keys[(positions.get key - 1).toNat]! key then
    .ok (s, values.get key)
  else
    .error .malformed

/-- Owner-gated insert-or-update. Insert commits key, position, value, then count as one EVM
transaction; update touches only the value namespace. Full growth uses the shared cap terminal. -/
@[pf_entry]
def write (s : State) (key value : UInt64) : Except Error (State × Bool) :=
  if Access.requireOwner s.admin then
    if !StorageEnumerableMap.wellFormed capU64 s.count then
      .error .malformed
    else if StorageEnumerableMap.absent (positions.get key) then
      if StorageEnumerableMap.isFull capU64 s.count then
        .ok (s, Effect.thenTrue Revert.capExceeded)
      else if h : s.count.toNat < 4 then
        .ok ({ s with keys := s.keys.set s.count.toNat key h, count := s.count + 1 },
          Effect.thenTrue
            (positions.put key (StorageEnumerableMap.insertPosition s.count) |||
              values.put key value))
      else
        .error .malformed
    else if StorageEnumerableMap.forged (positions.get key) s.count then
      .error .malformed
    else if StorageEnumerableMap.canUpdate capU64 s.count (positions.get key)
        s.keys[(positions.get key - 1).toNat]! key then
      .ok (s, Effect.thenTrue (values.put key value))
    else
      .error .malformed
  else
    .ok (s, Effect.thenTrue Access.ownerViolation)

/-- Owner-gated swap-remove. Exact absence is a no-write false result. Removed values are cleared;
middle removal repairs only the moved key's position because its value remains keyed by identity. -/
@[pf_entry]
def remove (s : State) (key : UInt64) : Except Error (State × Bool) :=
  if Access.requireOwner s.admin then
    if !StorageEnumerableMap.wellFormed capU64 s.count then
      .error .malformed
    else if StorageEnumerableMap.absent (positions.get key) then
      .ok (s, false)
    else if StorageEnumerableMap.forged (positions.get key) s.count then
      .error .malformed
    else if StorageEnumerableMap.canRemove capU64 s.count (positions.get key)
        s.keys[(positions.get key - 1).toNat]! key then
      if h : (positions.get key - 1).toNat < 4 then
        if StorageEnumerableMap.movesLast (positions.get key) s.count then
          if h2 : (s.count - 1).toNat < 4 then
            .ok ({ s with
                    keys := s.keys.set (positions.get key - 1).toNat
                      (s.keys[(s.count - 1).toNat]) h,
                    count := StorageEnumerableMap.removedCount s.count },
              Effect.thenTrue
                (positions.put (s.keys[(s.count - 1).toNat]) (positions.get key) |||
                  positions.put key 0 ||| values.put key 0))
          else
            .error .malformed
        else
          .ok ({ s with count := StorageEnumerableMap.removedCount s.count },
            Effect.thenTrue (positions.put key 0 ||| values.put key 0))
      else
        .error .malformed
    else
      .error .malformed
  else
    .ok (s, Effect.thenTrue Access.ownerViolation)

end Examples.EvmConfigMap
