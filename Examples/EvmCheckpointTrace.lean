import ProofForge
import ProofForge.Evm.Sdk.StorageCheckpoints

/-!
Permissionless capacity-3 consumer of the reusable bounded EVM checkpoint policy. Unlike the
owner-gated book, full growth and decreasing keys use application-owned typed errors. Equal
latest keys still overwrite without consuming capacity.
-/

namespace Examples.EvmCheckpointTrace

open ProofForge.Evm.Sdk

abbrev capacity : Nat := 3

@[pf_inline] def capU64 : UInt64 := 3

structure State where
  keys : Vector UInt64 3
  values : Vector UInt64 3
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  trace : StorageCheckpoints.Descriptor capacity

@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let trace := StorageCheckpoints.declare Storage.Static.Layout.root
    "keys" "values" "count" capacity
  { handle := { trace := trace.handle }, next := trace.next }

@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | unordered
  | full
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { keys := #v[0, 0, 0], values := #v[0, 0, 0], count := 0 }

@[pf_entry]
def sizeOf (s : State) : UInt64 :=
  s.count

@[pf_entry]
def latestValue (s : State) : UInt64 :=
  if StorageCheckpoints.wellFormed capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! 0 && 0 < s.count then
    s.values[(StorageCheckpoints.latestIndex s.count).toNat]!
  else
    StorageCheckpoints.emptyValue

@[pf_entry]
def lowerValue (s : State) (query : UInt64) : UInt64 :=
  if StorageCheckpoints.wellFormed capU64 s.count s.keys[0]! s.keys[1]! s.keys[2]! 0 then
    let index := StorageCheckpoints.lowerBoundIndex s.count query
      s.keys[0]! s.keys[1]! s.keys[2]! 0
    if StorageCheckpoints.hasLowerBound s.count index then s.values[index.toNat]!
    else StorageCheckpoints.emptyValue
  else
    StorageCheckpoints.emptyValue

@[pf_entry]
def push (s : State) (key value : UInt64) : Except Error (State × UInt64) :=
  if !StorageCheckpoints.wellFormed capU64 s.count s.keys[0]! s.keys[1]! s.keys[2]! 0 then
    .error .malformed
  else if StorageCheckpoints.canOverwrite capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! 0 key then
    let index := StorageCheckpoints.latestIndex s.count
    if h : index.toNat < 3 then
      .ok ({ s with values := s.values.set index.toNat value h }, value)
    else
      .error .malformed
  else if StorageCheckpoints.canAppend capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! 0 key then
    if h : s.count.toNat < 3 then
      .ok ({ s with
              keys := s.keys.set s.count.toNat key h,
              values := s.values.set s.count.toNat value h,
              count := StorageCheckpoints.appendedCount s.count }, value)
    else
      .error .malformed
  else if StorageCheckpoints.isDecreasing capU64 s.count
      s.keys[0]! s.keys[1]! s.keys[2]! 0 key then
    .error .unordered
  else if StorageCheckpoints.isFull capU64 s.count then
    .error .full
  else
    .error .unordered

end Examples.EvmCheckpointTrace
