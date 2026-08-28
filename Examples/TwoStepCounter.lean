import ProofForge
import ProofForge.Evm.Sdk.Access

namespace Examples.TwoStepCounter

open ProofForge.Evm.Sdk

/-!
EVM-SDK-1 consumer A: a counter guarded by `Access.requireOwner` /
`Access.requireRunning` with two-step ownership transfer via `Access.Ownership`.

The owner is an explicit `Address` state field (mutable so `acceptOwnership` can rotate
it); the paused flag is an explicit `UInt8` state field; nominations live in the single
`Ownership` hashed-map namespace. All storage writes stay in this file.
-/

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- owner: stored so two-step transfer can rotate it. paused: 0 running, 1 paused. -/
structure State where
  owner : Address
  paused : UInt8
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- One nomination namespace from the root cursor; no numeric base escapes. -/
@[pf_inline] def ownership : Access.Ownership :=
  Access.Ownership.allocate Storage.Layout.root |>.handle

@[pf_entry]
def init (owner : Address) : State :=
  { owner, paused := Access.runningFlag, count := 0 }

/-- Step 1 of ownership transfer: current owner nominates `candidate`.
    Non-owner → `Unauthorized(caller)`; zero candidate → `ZeroAddress()`. -/
@[pf_entry]
def transferOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Address.isZero candidate then
      .ok (s, Revert.zeroAddress)
    else
      .ok (s, ownership.nominate candidate)
  else
    .ok (s, Access.ownerViolation)

/-- Cancel a pending nomination. Non-owner → `Unauthorized(caller)`. -/
@[pf_entry]
def cancelOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    .ok (s, ownership.cancel candidate)
  else
    .ok (s, Access.ownerViolation)

/-- Step 2: the nominee accepts. The owner field write is explicit here; the SDK only
    consumes the nomination flag. Non-nominee → `Unauthorized(caller)`. -/
@[pf_entry]
def acceptOwnership (s : State) : Except Error (State × UInt64) :=
  if ownership.callerIsPending then
    .ok ({ owner := Context.caller, paused := s.paused, count := s.count },
      ownership.consume)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated, pause-gated increment. Non-owner → `Unauthorized(caller)`;
    paused → `Paused()`; overflow → error, no state change. -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Access.requireRunning s.paused then
      if s.count ≤ u64Max - delta then
        let next := s.count + delta
        .ok ({ owner := s.owner, paused := s.paused, count := next }, next)
      else
        .error .overflow
    else
      .ok (s, Access.runningViolation)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated pause. The `0 ≠ 1` guard marks the checked state transition for extraction,
    matching the existing EVM examples. -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if (0 : UInt64) ≠ 1 then
      .ok ({ owner := s.owner, paused := Access.pausedFlag, count := s.count }, 1)
    else
      .error .overflow
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated unpause. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if (0 : UInt64) ≠ 1 then
      .ok ({ owner := s.owner, paused := Access.runningFlag, count := s.count }, 0)
    else
      .error .overflow
  else
    .ok (s, Access.ownerViolation)

@[pf_entry]
def ownerOf (s : State) : Address :=
  s.owner

@[pf_entry]
def pendingOf (_s : State) (who : Address) : UInt64 :=
  ownership.nominationOf who

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

@[pf_entry]
def get (s : State) : UInt64 :=
  s.count

end Examples.TwoStepCounter
