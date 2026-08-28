import ProofForge

/-!
EVM-SDK-2 consumer B: address/bool scalars plus a fixed array of records, plus the EVM-SDK-3
bounded static writer role set (two explicit address fields after the `closed` flag).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`;
the handles are compile-time descriptor data erased before extraction, and every entry below
reads and writes state through ordinary typed `State` field/`Vector` accesses (including the
existing dynamic-index vector path for `seats`). Writer role decisions rebuild a
`Roles.Set2` value from the two explicit fields and every role write is a literal-slot field
update. `Tests/EvmStaticStorageSpec` proves the extracted slots and the `seats` vector entry
equal the declared layout; `Tests/EvmRolesSpec` pins the writer role slots and terminals.
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
  /-- Writer role slot 0 (EVM-SDK-3 roles slice); `Address.zero` = vacant. The two
  explicit fields rebuild `Roles.Set2` for decisions; writes are literal-slot updates. -/
  writer0 : Address
  /-- Writer role slot 1; `Address.zero` = vacant. -/
  writer1 : Address
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  admin : Storage.Static.Handle Address
  seats : Storage.Static.Handle (Vector Seat 3)
  closed : Storage.Static.Handle Bool
  writer0 : Storage.Static.Handle Address
  writer1 : Storage.Static.Handle Address

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let seats := admin.next.recordArray (α := Vector Seat 3) "seats"
    [("points", .u64), ("tier", .u8)] 3
  let closed := seats.next.bool "closed"
  let writer0 := closed.next.address "writer0"
  let writer1 := writer0.next.address "writer1"
  { handle := { admin := admin.handle, seats := seats.handle, closed := closed.handle,
                writer0 := writer0.handle, writer1 := writer1.handle }
    next := writer1.next }

/-- The accumulated static layout: slots `0..15` (`admin_w0..w2:8@0..2`,
`seats_<i>_points:8@3+2i`, `seats_<i>_tier:1@4+2i`, `closed:1@9`,
`writer0_w0..w2:8@10..12`, `writer1_w0..w2:8@13..15`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin
    seats := #v[{ points := 0, tier := 0 }, { points := 0, tier := 0 },
                { points := 0, tier := 0 }]
    closed := false
    writer0 := Address.zero
    writer1 := Address.zero }

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

/-- Admin-gated writer grant. Closed roster → `Paused()`; otherwise the pure `Roles.Set2`
decisions over the two explicit fields select the terminal or the literal-slot field write:
zero candidate → `ZeroAddress()`, duplicate → idempotent no-op, `grantSlot0`/`grantSlot1` →
explicit slot write, full set → `CapExceeded()`. -/
@[pf_entry]
def grantWriter (s : State) (who : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    if s.closed then
      .ok (s, Access.runningViolation)
    else
      let rs : Roles.Set2 := ⟨s.writer0, s.writer1⟩
      if Address.isZero who then
        .ok (s, Revert.zeroAddress)
      else if rs.member who then
        .ok (s, 0)
      else if rs.grantSlot0 who then
        .ok ({ s with writer0 := who }, 1)
      else if rs.grantSlot1 who then
        .ok ({ s with writer1 := who }, 1)
      else
        .ok (s, Revert.capExceeded)
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated writer revoke; the pure `Roles.Set2.revokeSlot0`/`revokeSlot1` decisions
select the literal-slot clear, and a nonmember candidate is an idempotent no-op. Closed
rosters still allow revocation so membership can be wound down. -/
@[pf_entry]
def revokeWriter (s : State) (who : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    let rs : Roles.Set2 := ⟨s.writer0, s.writer1⟩
    if rs.revokeSlot0 who then
      .ok ({ s with writer0 := Address.zero }, 1)
    else if rs.revokeSlot1 who then
      .ok ({ s with writer1 := Address.zero }, 1)
    else
      .ok (s, 0)
  else
    .ok (s, Access.ownerViolation)

/-- Membership view; same `ite`-wrapped view-return shape as `EvmStaticCounter.isOperator`. -/
@[pf_entry]
def isWriter (s : State) (who : Address) : Bool :=
  if Roles.Set2.member ⟨s.writer0, s.writer1⟩ who then true else false

end Examples.EvmStaticRoster
