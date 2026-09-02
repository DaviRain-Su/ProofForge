import ProofForge

namespace Examples.Evm.TwoStepCounter
open ProofForge.Evm.Sdk

/-!
EVM-SDK-1 consumer A: a counter guarded by `Access.requireOwner` /
`Pausable.isRunning` with two-step ownership transfer via `Access.Ownership`.

The owner is an explicit `Address` state field (mutable so `acceptOwnership` can rotate it), the
paused flag is an explicit `UInt8` state field, and `ownership` contains exactly one pending
address. All storage writes stay in this file.
-/

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- owner: stored so two-step transfer can rotate it. paused: 0 running, 1 paused. -/
structure State where
  owner : Address
  paused : UInt8
  count : UInt64
  ownership : Address
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (owner : Address) : State :=
  { owner, paused := Pausable.running, count := 0, ownership := Access.Ownership.none }

/-- Step 1 of ownership transfer: current owner nominates `candidate`.
    Non-owner → `Unauthorized(caller)`; zero candidate → `ZeroAddress()`. -/
@[pf_entry]
def transferOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Address.isZero candidate then
      .ok (s, Revert.zeroAddress)
    else
      .ok ({ s with ownership := Access.Ownership.nominate s.ownership candidate }, 1)
  else
    .ok (s, Access.ownerViolation)

/-- Cancel a pending nomination. Non-owner → `Unauthorized(caller)`. -/
@[pf_entry]
def cancelOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Access.Ownership.isPending s.ownership candidate then
      .ok ({ s with ownership := Access.Ownership.cancel s.ownership }, 0)
    else
      .ok (s, 0)
  else
    .ok (s, Access.ownerViolation)

/-- Step 2: the nominee accepts. The owner field write is explicit here; the SDK only
    consumes the nomination flag. Non-nominee → `Unauthorized(caller)`. -/
@[pf_entry]
def acceptOwnership (s : State) : Except Error (State × UInt64) :=
  if Access.Ownership.callerIsPending s.ownership then
    .ok ({ owner := Context.caller, paused := s.paused, count := s.count, ownership :=
      Access.Ownership.consume s.ownership }, 1)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated, pause-gated increment. Non-owner → `Unauthorized(caller)`;
    paused → `Paused()`; overflow → error, no state change. -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Pausable.isRunning s.paused then
      if s.count ≤ u64Max - delta then
        let next := s.count + delta
        .ok ({ s with count := next }, next)
      else
        .error .overflow
    else
      .ok (s, Pausable.violation)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated pause. -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    .ok ({ s with paused := Pausable.pause s.paused }, 1)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated unpause. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    .ok ({ s with paused := Pausable.unpause s.paused }, 0)
  else
    .ok (s, Access.ownerViolation)

@[pf_entry]
def ownerOf (s : State) : Address :=
  s.owner

@[pf_entry]
def pendingOf (_s : State) (who : Address) : UInt64 :=
  Access.Ownership.nominationOf _s.ownership who

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

@[pf_entry]
def get (s : State) : UInt64 :=
  s.count

end Examples.Evm.TwoStepCounter