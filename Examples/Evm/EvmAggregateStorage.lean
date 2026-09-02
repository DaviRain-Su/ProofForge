import ProofForge

/-!
Feature A aggregate-storage consumer: nested State (depth 2).

`declared` uses `Storage.Static.nestedRecord` so the compile-time leaf table matches Extract's
`bundle_amount` / `bundle_details_side` / `bundle_details_enabled` spelling. Methods return leaf
views, a flat product (`bundleSignal`), and nested product views (`bundleView` /
`detailsView`) — the nested product return × aggregate storage combination called out by
`evm-rt-nested-001`.
`runtime-tests/evm/anvil_aggregate_storage.sh` covers admin-gated nested writes, sibling-leaf
preservation, leaf views, flat/nested product views, and `bundleSignal`.
-/

namespace Examples.Evm.EvmAggregateStorage
open ProofForge.Evm.Sdk

/-- Nested leaf record: flattens under `bundle_details_side` / `bundle_details_enabled`. -/
structure Details where
  side : UInt8
  enabled : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Depth-2 aggregate: flattens to `bundle_amount` plus the nested details leaves. -/
structure Bundle where
  amount : UInt64
  details : Details
  deriving Repr, DecidableEq, Inhabited

structure State where
  admin : Address
  bundle : Bundle
  deriving Repr, DecidableEq, Inhabited

structure Handles where
  admin : Storage.Static.Handle Address
  bundle : Storage.Static.Handle Bundle

/-- Static layout in exact `State` declaration order. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let admin := Storage.Static.Layout.root.address "admin"
  let bundle := admin.next.nestedRecord (α := Bundle) "bundle"
    [ ("amount", .leaf .u64)
    , ("details", .record [("side", .u8), ("enabled", .bool)]) ]
  { handle := { admin := admin.handle, bundle := bundle.handle }
    next := bundle.next }

/-- Slots `0..5`: `admin_w0..w2`, `bundle_amount`, `bundle_details_side`,
`bundle_details_enabled`. -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin
    bundle := { amount := 0, details := { side := 0, enabled := false } } }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

/-- Nested aggregate leaf views from persistent storage. -/
@[pf_entry]
def amountOf (s : State) : UInt64 :=
  s.bundle.amount

@[pf_entry]
def sideOf (s : State) : UInt8 :=
  s.bundle.details.side

@[pf_entry]
def enabledOf (s : State) : Bool :=
  s.bundle.details.enabled

/-- Flat product projection from nested aggregate storage: `(amount, enabled)`. -/
@[pf_entry]
def bundleSignal (s : State) : UInt64 × Bool :=
  (s.bundle.amount, s.bundle.details.enabled)

/-- Nested product view of the full storage field tree: `(amount, (side, enabled))`.
Feature A depth-2 product return sourced from `nestedRecord` leaves (not a flat projection). -/
@[pf_entry]
def bundleView (s : State) : UInt64 × (UInt8 × Bool) :=
  (s.bundle.amount, (s.bundle.details.side, s.bundle.details.enabled))

/-- Nested details product from the storage field subtree: `(side, enabled)`. -/
@[pf_entry]
def detailsView (s : State) : UInt8 × Bool :=
  (s.bundle.details.side, s.bundle.details.enabled)

/-- Admin-gated nested aggregate write. -/
@[pf_entry]
def setBundle (s : State) (amount : UInt64) (side : UInt8) (enabled : Bool) :
    Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    .ok ({ s with bundle := { amount, details := { side, enabled } } }, amount)
  else
    .ok (s, Access.ownerViolation)

/-- Admin-gated nested field update that preserves sibling leaves. -/
@[pf_entry]
def setAmount (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    .ok ({ s with bundle := { s.bundle with amount } }, amount)
  else
    .ok (s, Access.ownerViolation)

end Examples.Evm.EvmAggregateStorage
