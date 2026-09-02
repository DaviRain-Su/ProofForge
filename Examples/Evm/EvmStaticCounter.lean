import ProofForge

/-!
EVM-SDK-2 consumer A: scalar/wide/record static storage declarations, plus the EVM-SDK-3
bounded static operator role set (two explicit address fields after the record fields).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`;
the handles are compile-time descriptor data erased before extraction, and every entry below
reads and writes state through ordinary typed `State` field access. Role decisions rebuild a
`Roles.Set2` value from the two explicit fields and every role write is a literal-slot field
update. `Tests/EvmStaticStorageSpec` and `Tests/EvmRolesSpec` prove the extracted slots
equal `layout.leaves`, so the declaration and the real flattening cannot drift apart.
-/

namespace Examples.Evm.EvmStaticCounter
open ProofForge.Evm.Sdk

/-- Flat record: flattens to `tally_count` / `tally_window`. -/
structure Tally where
  count : UInt64
  window : UInt16
  deriving Repr, DecidableEq, Inhabited

structure State where
  paused : UInt8
  total : UInt256
  tally : Tally
  /-- Operator role slot 0 (EVM-SDK-3 roles slice); `Address.zero` = vacant. The two
  explicit fields rebuild `Roles.Set2` for decisions; writes are literal-slot updates. -/
  operator0 : Address
  /-- Operator role slot 1; `Address.zero` = vacant. -/
  operator1 : Address
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  paused : Storage.Static.Handle UInt8
  total : Storage.Static.Handle UInt256
  tally : Storage.Static.Handle Tally
  operator0 : Storage.Static.Handle Address
  operator1 : Storage.Static.Handle Address

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let paused := Storage.Static.Layout.root.uint8 "paused"
  let total := paused.next.uint256 "total"
  let tally := total.next.record (α := Tally) "tally" [("count", .u64), ("window", .u16)]
  let operator0 := tally.next.address "operator0"
  let operator1 := operator0.next.address "operator1"
  { handle := { paused := paused.handle, total := total.handle, tally := tally.handle,
                operator0 := operator0.handle, operator1 := operator1.handle }
    next := operator1.next }

/-- The accumulated static layout: slots `0..12` (`paused:1@0`, `total_w0..w3:8@1..4`,
`tally_count:8@5`, `tally_window:2@6`, `operator0_w0..w2:8@7..9`,
`operator1_w0..w2:8@10..12`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (seed : UInt64) (_owner : Address) : State :=
  { paused := 0, total := ⟨seed, 0, 0, 0⟩, tally := { count := 0, window := 0 },
    operator0 := Address.zero, operator1 := Address.zero }

/-- Running-gated increment. Paused → `Paused()` revert value; overflow → typed error. -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireRunning s.paused then
    if s.tally.count ≤ u64Max - delta then
      let next := s.tally.count + delta
      .ok ({ s with total := UInt256.add s.total ⟨delta, 0, 0, 0⟩,
                    tally := { s.tally with count := next } }, next)
    else
      .error .overflow
  else
    .ok (s, Access.runningViolation)

/-- Owner-only window update; the owner is a constructor immutable. -/
@[pf_entry]
def setWindow (s : State) (window : UInt16) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with tally := { s.tally with window } }, window.toUInt64)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with paused := 1 }, 1)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with paused := 0 }, 0)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def countOf (s : State) : UInt64 :=
  s.tally.count

@[pf_entry]
def windowOf (s : State) : UInt16 :=
  s.tally.window

@[pf_entry]
def totalOf (s : State) : UInt256 :=
  s.total

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

/-- Immutable-owner-gated operator grant. The pure `Roles.Set2` decisions over the two
explicit fields select the terminal or the literal-slot field write: zero candidate →
`ZeroAddress()`, duplicate → idempotent no-op, `grantSlot0`/`grantSlot1` → explicit slot
write, full set → `CapExceeded()`. -/
@[pf_entry]
def grantOperator (s : State) (who : Address) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    let rs : Roles.Set2 := ⟨s.operator0, s.operator1⟩
    if Address.isZero who then
      .ok (s, Revert.zeroAddress)
    else if rs.member who then
      .ok (s, 0)
    else if rs.grantSlot0 who then
      .ok ({ s with operator0 := who }, 1)
    else if rs.grantSlot1 who then
      .ok ({ s with operator1 := who }, 1)
    else
      .ok (s, Revert.capExceeded)
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- Immutable-owner-gated operator revoke; the pure `Roles.Set2.revokeSlot0`/`revokeSlot1`
decisions select the literal-slot clear, and a nonmember candidate is an idempotent no-op. -/
@[pf_entry]
def revokeOperator (s : State) (who : Address) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    let rs : Roles.Set2 := ⟨s.operator0, s.operator1⟩
    if rs.revokeSlot0 who then
      .ok ({ s with operator0 := Address.zero }, 1)
    else if rs.revokeSlot1 who then
      .ok ({ s with operator1 := Address.zero }, 1)
    else
      .ok (s, 0)
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- Membership view. The `ite` wrapper is the view-return shape the current extractor lowers
(a bare component Boolean does not decode as a view body); the decision itself is the pure
`Roles.Set2.member` over the two explicit fields. -/
@[pf_entry]
def isOperator (s : State) (who : Address) : Bool :=
  if Roles.Set2.member ⟨s.operator0, s.operator1⟩ who then true else false

end Examples.Evm.EvmStaticCounter