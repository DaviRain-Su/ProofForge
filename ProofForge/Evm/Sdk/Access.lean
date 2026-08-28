import ProofForge.Evm.Sdk.Pausable

namespace ProofForge.Evm.Sdk.Access

/-!
Reusable EVM access-policy combinators (EVM-SDK-1).

This module owns contract *policy gates*, not storage geometry. Every combinator is
`@[pf_inline]` and erases at extraction into the existing target-owned components:

- gates read `Context.caller` and compare through `Address.eq` (the `WideWord`
  component query), or delegate an explicit `UInt8` paused flag to `Sdk.Pausable`;
  construction-time immutable owners keep using the existing `Address.eqImmutable` directly
  (e.g. `Examples.Token`),
- failure terminals are the closed `Revert` set (`Unauthorized(caller)`, `Paused()`),
  never new error selectors;
- two-step ownership is one fixed `Ownership` value containing the sole pending address; the
  consumer stores that value as ordinary static state, so an accepted transfer cannot leave an
  older nominee live in another map entry.

Storage writes stay explicit: `Ownership.nominate` / `cancel` / `consume` return replacement
values, while the consumer's state transition writes both ownership policy and owner/paused
fields. This module never performs a hidden storage write.

Resource contract: gates are O(1) component queries; `Ownership` is exactly one `Address` (three
EVM words in the current address representation). There is no loop, allocation, hashed namespace,
or hidden storage.

Component boundary (intentionally absent here):

- no reentrancy guard: a sound guard needs a typed external-call/effect-sequencing contract, and
  the current closed-call set must not be pretended pure;
- no roles or pause-state owner: use `Sdk.Roles.Set2` for bounded role decisions and
  `Sdk.Pausable` for explicit pause flags/transitions;
- no new revert errors: only the existing closed `Revert` set is composed.

The public `ProofForge.Evm.Sdk` umbrella exports this component. Nothing in this module requires
`Evm.Golden`, `Evm.Registry`, Ops, IR, or Emit changes.
-/

/-- Value of an explicit paused flag while the contract is running. -/
@[pf_inline] def runningFlag : UInt8 := Pausable.running

/-- Value of an explicit paused flag while the contract is paused. -/
@[pf_inline] def pausedFlag : UInt8 := Pausable.paused

/-- Owner gate: the caller holds the explicit stored-owner handle.
    Use as `if Access.requireOwner s.owner then … else .ok (s, Access.ownerViolation)`. -/
@[pf_inline] def requireOwner (owner : Address) : Bool :=
  Address.eq Context.caller owner

/-- Running gate: the explicit paused flag is clear.
    Use as `if Access.requireRunning s.paused then … else .ok (s, Access.runningViolation)`. -/
@[pf_inline] def requireRunning (paused : UInt8) : Bool :=
  Pausable.isRunning paused

/-- Failure terminal of the owner gate: `Unauthorized(caller)`. Returns the revert value;
    the caller's state is returned unchanged by the consumer. -/
@[pf_inline] def ownerViolation : UInt64 :=
  Revert.unauthorized Context.caller

/-- Failure terminal of the running gate: `Paused()`. -/
@[pf_inline] def runningViolation : UInt64 :=
  Pausable.violation

/-- Explicit single-pending-owner state. The current owner remains a separate consumer field; this
value is either one nonzero nominee or `Address.zero`. The alias deliberately reuses the existing
fixed address schema instead of requiring a policy-specific codec or target operation. -/
abbrev Ownership := Address

namespace Ownership

/-- Canonical state with no pending nominee. -/
@[pf_inline] def none : Address :=
  Address.zero

/-- True exactly when one nonzero pending address equals `who`. -/
@[pf_inline] def isPending (o : Ownership) (who : Address) : Bool :=
  !Address.isZero o && Address.eq o who

/-- Accept gate: the caller is the current nominee.
    Use as `if ownership.callerIsPending then … else .ok (s, Access.ownerViolation)`. -/
@[pf_inline] def callerIsPending (o : Ownership) : Bool :=
  Ownership.isPending o Context.caller

/-- Replace the sole nominee. The consumer explicitly stores the returned value and must gate the
operation with `Access.requireOwner` and reject the zero address. -/
@[pf_inline] def nominate (_o : Ownership) (candidate : Address) : Address :=
  candidate

/-- Clear the sole nomination. The consumer explicitly stores the returned value. -/
@[pf_inline] def cancel (_o : Ownership) : Address :=
  Ownership.none

/-- Consume the sole nomination during `acceptOwnership`. -/
@[pf_inline] def consume (o : Ownership) : Address :=
  Ownership.cancel o

/-- Read a compatibility flag for `who`: `1` only for the sole current nominee. -/
@[pf_inline] def nominationOf (o : Ownership) (who : Address) : UInt64 :=
  if Ownership.isPending o who then 1 else 0

end Ownership

end ProofForge.Evm.Sdk.Access
