import ProofForge
import ProofForge.Evm.Sdk.StorageRing

/-!
Ring-queue consumer B: a permissionless bounded event-history workflow — dequeue, clear, then
refill across the wrap boundary — over the `Evm.Sdk.StorageRing` persistent circular-buffer
policy (capacity 3).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageRing.Descriptor` bundle is compile-time data erased before extraction. Every entry reads
and writes state through ordinary typed `State` field/`Vector` accesses: the SDK owns only the
head/length/slot decisions (`canPush`/`canPop`/`absIndex`/`poppedHead`), and each physical write
is a visible literal field update. `Tests/EvmStorageRingSpec` proves the extracted slots and the
`tape` vector entry equal the declared layout, and `runtime-tests/evm/anvil_ring_history.sh`
covers the drain/clear/refill/wraparound and malformed matrix.

Policy differences from `Examples.EvmRingMailbox`: no owner at all (permissionless), an
enqueue on a full tape reverts with the typed `full()` error instead of `CapExceeded()`, and
`reset` returns the physical tail slot that received each enqueue so the wraparound reuse of
backing slots is observable on the wire.
-/

namespace Examples.EvmRingHistory

open ProofForge.Evm.Sdk

/-- Compile-time capacity of the history's backing ring. -/
abbrev capacity : Nat := 3

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `3`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`, `EvmVecLog`). -/
@[pf_inline] def capU64 : UInt64 := 3

structure State where
  /-- Fixed backing field of the bounded history; only the live ring described by `head` and
  `live` is reachable. -/
  tape : Vector UInt64 3
  /-- Physical index of the history front (`0..2`; canonical `0` while empty). -/
  head : UInt64
  /-- Live event count (`0..3`). -/
  live : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  history : StorageRing.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let history := StorageRing.declare Storage.Static.Layout.root "tape" "head" "live" capacity
  { handle := { history := history.handle }, next := history.next }

/-- The accumulated static layout: slots `0..4` (`tape_<i>:8@0..2`, `head:8@3`, `live:8@4`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | full
  | empty
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Constructor seeds one genesis event so deployment exercises the ring + metadata stores. -/
@[pf_entry]
def init (first : UInt64) : State :=
  { tape := #v[first, 0, 0], head := 0, live := 1 }

@[pf_entry]
def liveOf (s : State) : UInt64 :=
  s.live

@[pf_entry]
def headOf (s : State) : UInt64 :=
  s.head

/-- Front view: the oldest live event, or `0` when the history is empty or the persisted
metadata is malformed. -/
@[pf_entry]
def currentOf (s : State) : UInt64 :=
  if StorageRing.canPeek capU64 s.head s.live then
    if h : s.head.toNat < 3 then s.tape[s.head.toNat] else 0
  else
    0

/-- Permissionless enqueue at the ring tail; returns the physical slot that received the event so
wraparound reuse is observable. Malformed metadata fails with the typed terminal and a canonical
full tape has its own typed `full` error, both before any store. The physical write is the
literal update of `tape[absIndex head live]` plus `live + 1`; head is unchanged. -/
@[pf_entry]
def append (s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if StorageRing.wellFormed capU64 s.head s.live then
    if StorageRing.canPush capU64 s.head s.live then
      let tail := StorageRing.absIndex s.head s.live capU64
      if h : tail.toNat < 3 then
        let next := s.live + 1
        .ok ({ s with tape := s.tape.set tail.toNat value h, live := next }, tail)
      else
        .error .malformed
    else
      .error .full
  else
    .error .malformed

/-- Permissionless dequeue: returns the front value and stores `poppedHead` (canonical `0` when
the tape empties) plus `live - 1`. An empty or malformed tape has a distinct typed error before
any store; the popped slot keeps its stale value and stays unreachable. -/
@[pf_entry]
def advance (s : State) : Except Error (State × UInt64) :=
  if StorageRing.wellFormed capU64 s.head s.live then
    if StorageRing.canPop capU64 s.head s.live then
      if h : s.head.toNat < 3 then
        let value := s.tape[s.head.toNat]
        let nextHead := StorageRing.poppedHead s.head s.live capU64
        .ok ({ s with head := nextHead, live := s.live - 1 }, value)
      else
        .error .malformed
    else
      .error .empty
  else
    .error .malformed

/-- Permissionless clear: only the metadata slots reset to the canonical empty state (head `0`,
live `0`). Backing slots keep their stale values and stay unreachable until future appends
overwrite them; malformed metadata fails before the store instead of being silently repaired. -/
@[pf_entry]
def reset (s : State) : Except Error (State × UInt64) :=
  if StorageRing.canClear capU64 s.head s.live then
    .ok ({ s with head := StorageRing.clearedHead, live := StorageRing.clearedLive }, 0)
  else
    .error .malformed

end Examples.EvmRingHistory
