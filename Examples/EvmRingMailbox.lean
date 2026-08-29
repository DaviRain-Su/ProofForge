import ProofForge
import ProofForge.Evm.Sdk.StorageRing

/-!
Ring-queue consumer A: an owner-gated mailbox that rejects delivery when full, over the
`Evm.Sdk.StorageRing` persistent circular-buffer policy (capacity 4).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageRing.Descriptor` bundle is compile-time data erased before extraction. Every entry reads
and writes state through ordinary typed `State` field/`Vector` accesses: the SDK owns only the
head/length/slot decisions (`canPush`/`canPop`/`canGet`/`absIndex`/`poppedHead`), and each
physical write is a visible literal field update. `Tests/EvmStorageRingSpec` proves the
extracted slots and the `pending` vector entry equal the declared layout, and
`runtime-tests/evm/anvil_ring_mailbox.sh` covers the wraparound, full/empty/malformed, and
unauthorized matrix.

Policy differences from `Examples.EvmRingHistory`: this mailbox is owner-gated, rejects a full
mailbox with the `CapExceeded()` revert value (instead of a typed `full()` error), returns the
live count after a delivery, and never exposes runtime-indexed writes.
-/

namespace Examples.EvmRingMailbox

open ProofForge.Evm.Sdk

/-- Compile-time capacity of the mailbox's backing ring. -/
abbrev capacity : Nat := 4

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `4`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`, `EvmVecLog`). -/
@[pf_inline] def capU64 : UInt64 := 4

structure State where
  admin : Address
  /-- Fixed backing field of the bounded mailbox; only the live ring described by `head` and
  `live` is reachable. -/
  pending : Vector UInt64 4
  /-- Physical index of the mailbox front (`0..3`; canonical `0` while empty). -/
  head : UInt64
  /-- Live message count (`0..4`). -/
  live : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  admin : Storage.Static.Handle Address
  queue : StorageRing.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let queue := StorageRing.declare admin.next "pending" "head" "live" capacity
  { handle := { admin := admin.handle, queue := queue.handle }, next := queue.next }

/-- The accumulated static layout: slots `0..7` (`admin_w0..w2:8@0..2`, `pending_<i>:8@3..6`,
`head:8@7`, `live:8@8`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | empty
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, pending := #v[0, 0, 0, 0], head := 0, live := 0 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def liveOf (s : State) : UInt64 :=
  s.live

@[pf_entry]
def headOf (s : State) : UInt64 :=
  s.head

/-- Front message view: the oldest live message, or `0` when the mailbox is empty or the
persisted metadata is malformed. -/
@[pf_entry]
def frontOf (s : State) : UInt64 :=
  if StorageRing.canPeek capU64 s.head s.live then
    if h : s.head.toNat < 4 then s.pending[s.head.toNat] else 0
  else
    0

/-- Runtime-indexed read: live offset `offset` from the front (after the ring wraps past the
physical end, the live order continues at slot 0), or the `0` fallback when the offset is out
of the live range or the persisted metadata is malformed. -/
@[pf_entry]
def messageAt (s : State) (offset : UInt64) : UInt64 :=
  if StorageRing.canGet capU64 s.head s.live offset then
    let slot := StorageRing.absIndex s.head offset capU64
    if h : slot.toNat < 4 then s.pending[slot.toNat] else 0
  else
    0

/-- Admin-gated delivery at the ring tail. Malformed metadata fails with the typed terminal
before any store; a canonical but full mailbox uses `CapExceeded()`. The physical writes are the
literal field update of `pending[absIndex head live]` plus `live + 1`. The inner compiler
guard's `else` is unreachable under an admissible decision. -/
@[pf_entry]
def deliver (s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageRing.wellFormed capU64 s.head s.live then
      if StorageRing.canPush capU64 s.head s.live then
        let tail := StorageRing.absIndex s.head s.live capU64
        if h : tail.toNat < 4 then
          let next := s.live + 1
          .ok ({ s with pending := s.pending.set tail.toNat value h, live := next }, next)
        else
          .error .malformed
      else
        .ok (s, Revert.capExceeded)
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated retrieval of the oldest message: returns the front value, advances the head
around the ring (canonical `0` when the mailbox empties), and stores `live - 1`. An empty or
malformed mailbox has a distinct typed error before any store; the popped slot keeps its stale
value and stays unreachable. -/
@[pf_entry]
def take (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageRing.wellFormed capU64 s.head s.live then
      if StorageRing.canPop capU64 s.head s.live then
        if h : s.head.toNat < 4 then
          let value := s.pending[s.head.toNat]
          let nextHead := StorageRing.poppedHead s.head s.live capU64
          .ok ({ s with head := nextHead, live := s.live - 1 }, value)
        else
          .error .malformed
      else
        .error .empty
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated clear: only the metadata slots reset to the canonical empty state (head `0`,
live `0`). Backing slots keep their stale values and stay unreachable until future deliveries
overwrite them; malformed metadata fails before the store instead of being silently repaired. -/
@[pf_entry]
def purge (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageRing.canClear capU64 s.head s.live then
      .ok ({ s with head := StorageRing.clearedHead, live := StorageRing.clearedLive }, 0)
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

end Examples.EvmRingMailbox
