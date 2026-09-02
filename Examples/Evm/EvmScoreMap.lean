import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableMap

/-!
Permissionless capacity-3 UInt64 score table. It independently consumes the same bounded
enumerable-map descriptor and decisions as `EvmConfigMap`, but uses a typed `full()` terminal and
non-reverting malformed lookup fallback. This keeps application policy outside the SDK while the
physical map invariant and O(1) mutation shape remain shared.
-/

namespace Examples.Evm.EvmScoreMap
open ProofForge.Evm.Sdk

abbrev capacity : Nat := 3

@[pf_inline] def capU64 : UInt64 := 3

structure State where
  players : Vector UInt64 3
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  scores : StorageEnumerableMap.Descriptor capacity

@[pf_inline] def positionAllocation := Storage.Layout.root.u64Map
@[pf_inline] def valueAllocation := positionAllocation.next.u64Map

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let scores := StorageEnumerableMap.declare Storage.Static.Layout.root "players" "count"
    positionAllocation.handle valueAllocation.handle capacity
  { handle := { scores := scores.handle }, next := scores.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next
@[pf_inline] def positions : Storage.U64Map := positionAllocation.handle
@[pf_inline] def values : Storage.U64Map := valueAllocation.handle

inductive Error where
  | full
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { players := #v[0, 0, 0], count := 0 }

@[pf_entry]
def sizeOf (s : State) : UInt64 := s.count

@[pf_entry]
def playerAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableMap.canEntryAt capU64 s.count index then s.players[index.toNat]! else 0

@[pf_entry]
def scoreAt (s : State) (index : UInt64) : UInt64 :=
  if StorageEnumerableMap.canEntryAt capU64 s.count index then
    values.get s.players[index.toNat]!
  else
    0

/-- Non-reverting view: malformed metadata is indistinguishable from absence and returns zero. -/
@[pf_entry]
def scoreOf (s : State) (player : UInt64) : UInt64 :=
  if !StorageEnumerableMap.wellFormed capU64 s.count then 0
  else if StorageEnumerableMap.absent (positions.get player) then 0
  else if StorageEnumerableMap.forged (positions.get player) s.count then 0
  else if StorageEnumerableMap.isPresent (positions.get player) s.count
      s.players[(positions.get player - 1).toNat]! player then
    values.get player
  else
    0

@[pf_entry]
def put (s : State) (player score : UInt64) : Except Error (State × Bool) :=
  if !StorageEnumerableMap.wellFormed capU64 s.count then
    .error .malformed
  else if StorageEnumerableMap.absent (positions.get player) then
    if StorageEnumerableMap.isFull capU64 s.count then
      .error .full
    else if h : s.count.toNat < 3 then
      .ok ({ s with players := s.players.set s.count.toNat player h, count := s.count + 1 },
        Effect.thenTrue
          (positions.put player (StorageEnumerableMap.insertPosition s.count) |||
            values.put player score))
    else
      .error .malformed
  else if StorageEnumerableMap.forged (positions.get player) s.count then
    .error .malformed
  else if StorageEnumerableMap.canUpdate capU64 s.count (positions.get player)
      s.players[(positions.get player - 1).toNat]! player then
    .ok (s, Effect.thenTrue (values.put player score))
  else
    .error .malformed

@[pf_entry]
def erase (s : State) (player : UInt64) : Except Error (State × Bool) :=
  if !StorageEnumerableMap.wellFormed capU64 s.count then
    .error .malformed
  else if StorageEnumerableMap.absent (positions.get player) then
    .ok (s, false)
  else if StorageEnumerableMap.forged (positions.get player) s.count then
    .error .malformed
  else if StorageEnumerableMap.canRemove capU64 s.count (positions.get player)
      s.players[(positions.get player - 1).toNat]! player then
    if h : (positions.get player - 1).toNat < 3 then
      if StorageEnumerableMap.movesLast (positions.get player) s.count then
        if h2 : (s.count - 1).toNat < 3 then
          .ok ({ s with
                  players := s.players.set (positions.get player - 1).toNat
                    (s.players[(s.count - 1).toNat]) h,
                  count := StorageEnumerableMap.removedCount s.count },
            Effect.thenTrue
              (positions.put (s.players[(s.count - 1).toNat]) (positions.get player) |||
                positions.put player 0 ||| values.put player 0))
        else
          .error .malformed
      else
        .ok ({ s with count := StorageEnumerableMap.removedCount s.count },
          Effect.thenTrue (positions.put player 0 ||| values.put player 0))
    else
      .error .malformed
  else
    .error .malformed

end Examples.Evm.EvmScoreMap