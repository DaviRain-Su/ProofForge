import ProofForge
import ProofForge.Evm.Sdk.StorageCheckpoints

/-!
Owner-gated capacity-4 consumer of the reusable bounded EVM checkpoint policy. The SDK owns
strict key ordering, latest-overwrite, append, and lower-bound decisions; this application owns
authorization and the literal static State writes.
-/

namespace Examples.EvmCheckpointBook

open ProofForge.Evm.Sdk

abbrev capacity : Nat := 4

@[pf_inline] def capU64 : UInt64 := 4

structure State where
  admin : Address
  keys : Vector UInt64 4
  values : Vector UInt64 4
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  admin : Storage.Static.Handle Address
  trace : StorageCheckpoints.Descriptor capacity

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let trace := StorageCheckpoints.declare admin.next "keys" "values" "count" capacity
  { handle := { admin := admin.handle, trace := trace.handle }, next := trace.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | unordered
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, keys := #v[0, 0, 0, 0], values := #v[0, 0, 0, 0], count := 0 }

@[pf_entry]
def countOf (s : State) : UInt64 :=
  s.count

@[pf_entry]
def latestValue (s : State) : UInt64 :=
  if StorageCheckpoints.wellFormed capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! && 0 < s.count then
    s.values[(StorageCheckpoints.latestIndex s.count).toNat]!
  else
    StorageCheckpoints.emptyValue

@[pf_entry]
def lowerValue (s : State) (query : UInt64) : UInt64 :=
  if StorageCheckpoints.wellFormed capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! then
    let index := StorageCheckpoints.lowerBoundIndex s.count query
      s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]!
    if StorageCheckpoints.hasLowerBound s.count index then s.values[index.toNat]!
    else StorageCheckpoints.emptyValue
  else
    StorageCheckpoints.emptyValue

@[pf_entry]
def push (s : State) (key value : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if !StorageCheckpoints.wellFormed capU64 s.count
        s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! then
      .error .malformed
    else if StorageCheckpoints.canOverwrite capU64 s.count
        s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! key then
      let index := StorageCheckpoints.latestIndex s.count
      if h : index.toNat < 4 then
        .ok ({ s with values := s.values.set index.toNat value h }, s.count)
      else
        .error .malformed
    else if StorageCheckpoints.canAppend capU64 s.count
        s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! key then
      if h : s.count.toNat < 4 then
        .ok ({ s with
                keys := s.keys.set s.count.toNat key h,
                values := s.values.set s.count.toNat value h,
                count := StorageCheckpoints.appendedCount s.count },
          StorageCheckpoints.appendedCount s.count)
      else
        .error .malformed
    else if StorageCheckpoints.isDecreasing capU64 s.count
        s.keys[0]! s.keys[1]! s.keys[2]! s.keys[3]! key then
      .error .unordered
    else if StorageCheckpoints.isFull capU64 s.count then
      .ok (s, Revert.capExceeded)
    else
      .error .unordered
  else
    .ok (s, Access.ownerViolation)

end Examples.EvmCheckpointBook
