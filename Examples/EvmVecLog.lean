import ProofForge

/-!
R5-010 consumer A: an owner-gated bounded audit log over the `Evm.Sdk.StorageVec` persistent
vector policy (capacity 4).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageVec.Descriptor` bundle is compile-time data erased before extraction. Every entry reads
and writes state through ordinary typed `State` field/`Vector` accesses: the SDK owns only the
length/index decisions (`canPush`/`canSet`/`canGet`), and each physical write is a visible
literal field update. `Tests/EvmStorageVecSpec` proves the extracted slots and the `entries`
vector entry equal the declared layout, and `runtime-tests/evm/anvil_vec_log.sh` covers the
full/OOB/malformed/stale-slot matrix.
-/

namespace Examples.EvmVecLog

open ProofForge.Evm.Sdk

/-- Compile-time capacity of the log's backing vector. -/
abbrev capacity : Nat := 4

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `4`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`). -/
@[pf_inline] def capU64 : UInt64 := 4

structure State where
  admin : Address
  /-- Fixed backing field of the bounded log; only the active prefix `entries[0..count)` is
  reachable. -/
  entries : Vector UInt64 4
  /-- Explicit runtime length of the log. -/
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  admin : Storage.Static.Handle Address
  log : StorageVec.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let log := StorageVec.declare admin.next "entries" "count" capacity
  { handle := { admin := admin.handle, log := log.handle }, next := log.next }

/-- The accumulated static layout: slots `0..7` (`admin_w0..w2:8@0..2`,
`entries_<i>:8@3..6`, `count:8@7`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | oob
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, entries := #v[0, 0, 0, 0], count := 0 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def countOf (s : State) : UInt64 :=
  s.count

/-- Checked active-prefix read: the SDK `canGet` decision admits exactly `index < count` on a
well-formed length; OOB and malformed reads return the `0` fallback without reverting. -/
@[pf_entry]
def entryAt (s : State) (index : UInt64) : UInt64 :=
  if StorageVec.canGet capU64 s.count index then s.entries[index.toNat]! else 0

/-- Admin-gated append. Malformed length fails with the typed terminal; a canonical full log uses
`CapExceeded()`. The physical write is the literal field update of `entries[count]` plus
`count + 1`. The inner compiler guard's `else` is unreachable under an admissible decision. -/
@[pf_entry]
def record (s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageVec.wellFormed capU64 s.count then
      if StorageVec.canPush capU64 s.count then
        if h : s.count.toNat < 4 then
          let next := s.count + 1
          .ok ({ s with entries := s.entries.set s.count.toNat value h, count := next }, next)
        else
          .error .malformed
      else
        .ok (s, Revert.capExceeded)
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated overwrite of one active entry. Malformed length and canonical OOB index have
distinct typed terminals; the write touches only `entries[index]`. -/
@[pf_entry]
def amend (s : State) (index value : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageVec.wellFormed capU64 s.count then
      if StorageVec.canSet capU64 s.count index then
        if h : index.toNat < 4 then
          .ok ({ s with entries := s.entries.set index.toNat value h }, value)
        else
          .error .malformed
      else
        .error .oob
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated clear: only the length field resets to zero. Backing slots keep their stale
values and stay unreachable until future records overwrite them; malformed length fails before
the store instead of being silently repaired. -/
@[pf_entry]
def wipe (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if StorageVec.canClear capU64 s.count then
      .ok ({ s with count := StorageVec.clearedLength }, 0)
    else
      .error .malformed
  else
    .ok (s, Access.ownerViolation)

end Examples.EvmVecLog
