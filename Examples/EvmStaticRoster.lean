import ProofForge

/-!
EVM-SDK-2 consumer B: address/bool scalars plus a fixed array of records.

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`;
the handles are compile-time descriptor data erased before extraction, and every entry below
reads and writes state through ordinary typed `State` field/`Vector` accesses (including the
existing dynamic-index vector path). `Tests/EvmStaticStorageSpec` proves the extracted slots
and the `seats` vector entry equal the declared layout.
-/

namespace Examples.EvmStaticRoster

open ProofForge.Evm.Sdk

/-- Flat record element: flattens to `seats_<i>_points` / `seats_<i>_tier`. -/
structure Seat where
  points : UInt64
  tier : UInt8
  deriving Repr, DecidableEq, Inhabited

structure State where
  admin : Address
  seats : Vector Seat 3
  closed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  admin : Storage.Static.Handle Address
  seats : Storage.Static.Handle (Vector Seat 3)
  closed : Storage.Static.Handle Bool

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let seats := admin.next.recordArray (α := Vector Seat 3) "seats"
    [("points", .u64), ("tier", .u8)] 3
  let closed := seats.next.bool "closed"
  { handle := { admin := admin.handle, seats := seats.handle, closed := closed.handle }
    next := closed.next }

/-- The accumulated static layout: slots `0..9` (`admin_w0..w2:8@0..2`,
`seats_<i>_points:8@3+2i`, `seats_<i>_tier:1@4+2i`, `closed:1@9`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin
    seats := #v[{ points := 0, tier := 0 }, { points := 0, tier := 0 },
                { points := 0, tier := 0 }]
    closed := false }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def seatPoints (s : State) (index : UInt64) : UInt64 :=
  if h : index.toNat < 3 then s.seats[index.toNat].points else 0

@[pf_entry]
def seatTier (s : State) (index : UInt64) : UInt8 :=
  if h : index.toNat < 3 then s.seats[index.toNat].tier else 0

/-- Admin-gated seat update through the existing dynamic-index vector write path. -/
@[pf_entry]
def setSeat (s : State) (index : UInt64) (points : UInt64) (tier : UInt8) :
    Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if s.closed then
      .ok (s, Access.runningViolation)
    else
      if h : index.toNat < 3 then
        .ok ({ s with seats := s.seats.set index.toNat { points, tier } }, points)
      else
        .error .overflow
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated close; a closed roster rejects further seat updates by policy above. -/
@[pf_entry]
def close (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    .ok ({ s with closed := true }, 1)
  else
    .ok (s, Access.ownerViolation)

@[pf_entry]
def closedOf (s : State) : Bool :=
  s.closed

end Examples.EvmStaticRoster
