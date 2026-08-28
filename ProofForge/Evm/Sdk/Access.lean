import ProofForge.Evm.Sdk

namespace ProofForge.Evm.Sdk.Access

/-!
Reusable EVM access-policy combinators (EVM-SDK-1).

This module owns contract *policy gates*, not storage geometry. Every combinator is
`@[pf_inline]` and erases at extraction into the existing target-owned components:

- gates read `Context.caller` and compare through `Address.eq` (the `WideWord`
  component query), or test an explicit `UInt8` paused flag; construction-time immutable
  owners keep using the existing `Address.eqImmutable` directly (e.g. `Examples.Token`),
- failure terminals are the closed `Revert` set (`Unauthorized(caller)`, `Paused()`),
  never new error selectors;
- two-step nominations live in one typed hashed-map namespace
  (`Storage.AddressMap`, candidate ↦ 1), allocated from the consumer's `Storage.Layout`
  cursor so no numeric map base escapes into contract code.

Storage writes stay explicit: `Ownership.nominate` / `cancel` / `consume` are the typed
map writes performed at the call site, and the owner/paused fields themselves are ordinary
consumer-owned `State` fields updated by the consumer's own transition. This module never
writes the owner field; `acceptOwnership` in a consumer does that explicitly.

Resource contract: gates are O(1) component queries; an `Ownership` handle reserves exactly
one hashed-map namespace. There is no bounded loop, allocation, or hidden storage.

Fail-closed boundary (later dependencies, intentionally absent here):

- no reentrancy guard: a sound guard needs the typed external-call contract of EVM-RT-2
  (`EVM-SDK-3` consumes it), and the current closed-call set must not be pretended pure;
- no roles API: bounded role storage needs scalar/static storage declarations
  (EVM-SDK-2) or an owned role-namespace policy not yet specified;
- no new revert errors: only the existing closed `Revert` set is composed.

Integration hook: this module is imported directly by consumers
(`import ProofForge.Evm.Sdk.Access`). Registry/digest wiring of new example contracts and
the umbrella imports (`Examples.lean`, `Tests.lean`) are left to the coordinator; nothing
in this module requires `Evm.Golden`, `Evm.Registry`, Ops, IR, or Emit changes.
-/

/-- Value of an explicit paused flag while the contract is running. -/
@[pf_inline] def runningFlag : UInt8 := 0

/-- Value of an explicit paused flag while the contract is paused. -/
@[pf_inline] def pausedFlag : UInt8 := 1

/-- Owner gate: the caller holds the explicit stored-owner handle.
    Use as `if Access.requireOwner s.owner then … else .ok (s, Access.ownerViolation)`. -/
@[pf_inline] def requireOwner (owner : Address) : Bool :=
  Address.eq Context.caller owner

/-- Running gate: the explicit paused flag is clear.
    Use as `if Access.requireRunning s.paused then … else .ok (s, Access.runningViolation)`. -/
@[pf_inline] def requireRunning (paused : UInt8) : Bool :=
  paused == 0

/-- Failure terminal of the owner gate: `Unauthorized(caller)`. Returns the revert value;
    the caller's state is returned unchanged by the consumer. -/
@[pf_inline] def ownerViolation : UInt64 :=
  Revert.unauthorized Context.caller

/-- Failure terminal of the running gate: `Paused()`. -/
@[pf_inline] def runningViolation : UInt64 :=
  Revert.paused

/--
Explicit two-step ownership handle. The current owner stays wherever the consumer keeps it
(typically an `Address` state field); this handle owns only the pending-nomination
namespace: `candidate ↦ 1` while a transfer is proposed, absent/`0` otherwise.

Allocation is a compile-time `Storage.Layout` cursor step, so the namespace is disjoint
from every other map the consumer declares. The handle carries no runtime geometry.
-/
structure Ownership where
  pending : Storage.AddressMap
  deriving Repr, Inhabited

attribute [pf_inline] Ownership.pending

/-- Reserve one hashed-map namespace for nominations and advance the layout cursor.
    Keep the body projection-reducible (no `let`): extraction must see closed Nat
    geometry, matching the `Storage.Layout` descriptor contract. -/
@[pf_inline] def Ownership.allocate (layout : Storage.Layout) : Storage.Allocated Ownership :=
  { handle := { pending := layout.addressMap.handle }, next := layout.addressMap.next }

namespace Ownership

/-- True while `who` holds a pending nomination. The gate is a `≠ 0` test on the flag,
    the UInt64-map condition shape extraction supports; a `UInt256 ≥ 1` comparison against
    a constant bound is *not* a supported condition shape and must not be used here. -/
@[pf_inline] def isPending (o : Ownership) (who : Address) : Bool :=
  o.pending.get who != 0

/-- Accept gate: the caller is the current nominee.
    Use as `if ownership.callerIsPending then … else .ok (s, Access.ownerViolation)`. -/
@[pf_inline] def callerIsPending (o : Ownership) : Bool :=
  o.isPending Context.caller

/-- Nominate `candidate`. This is the explicit storage write behind `transferOwnership`;
    callers must gate it with `Access.requireOwner` (and usually reject the zero address). -/
@[pf_inline] def nominate (o : Ownership) (candidate : Address) : UInt64 :=
  o.pending.put candidate 1

/-- Cancel a nomination before it is accepted (explicit storage write, owner-gated by the
    caller). -/
@[pf_inline] def cancel (o : Ownership) (candidate : Address) : UInt64 :=
  o.pending.put candidate 0

/-- Consume the caller's nomination during `acceptOwnership` (explicit storage write).
    The consumer writes its own owner field in the same transition; this module does not. -/
@[pf_inline] def consume (o : Ownership) : UInt64 :=
  o.pending.put Context.caller 0

/-- Read the raw nomination flag for `who` (view helper; 1 while nominated, else 0). -/
@[pf_inline] def nominationOf (o : Ownership) (who : Address) : UInt64 :=
  o.pending.get who

end Ownership

end ProofForge.Evm.Sdk.Access
