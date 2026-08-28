import ProofForge
import ProofForge.Evm.Sdk.Access

namespace Examples.Credits

open ProofForge.Evm.Sdk

/-!
EVM-SDK-1 consumer B (independent of `Examples.TwoStepCounter`): an owner-granted credit
ledger. Reuses the same `Access` gates and `Access.Ownership` two-step transfer, plus a
second hashed-map namespace for per-account credits, demonstrating that one
`Storage.Layout` cursor keeps the policy namespace and the business namespace disjoint.

State: stored `owner` (rotated by two-step transfer), explicit `paused` flag, and a
`UInt256` `total` of claimed credits. Maps: `ownership` nominations (namespace 0) and
`credits` (namespace 1), both `AddressMap256` — the map shape whose get/condition/put
binding `Examples.Token` already proves end to end. All storage writes stay in this file.
-/

structure State where
  owner : Address
  paused : UInt8
  total : UInt256
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Static cursor: nominations take namespace 0, credits namespace 1. -/
@[pf_inline] def ownership : Access.Ownership :=
  Access.Ownership.allocate Storage.Layout.root |>.handle

@[pf_inline] def credits : Storage.AddressMap256 :=
  Access.Ownership.allocate Storage.Layout.root |>.next |>.addressMap256 |>.handle
@[pf_entry]
def init (owner : Address) : State :=
  { owner, paused := Access.runningFlag, total := UInt256.zero }

/-- Owner nominates `candidate` for the two-step transfer. -/
@[pf_entry]
def transferOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Address.isZero candidate then
      .ok (s, Revert.zeroAddress)
    else
      .ok (s, ownership.nominate candidate)
  else
    .ok (s, Access.ownerViolation)

/-- Nominee accepts; the owner-field write is explicit here. -/
@[pf_entry]
def acceptOwnership (s : State) : Except Error (State × UInt64) :=
  if ownership.callerIsPending then
    if (0 : UInt64) ≠ 1 then
      .ok ({ owner := Context.caller, paused := s.paused, total := s.total },
        ownership.consume)
    else
      .error .overflow
  else
    .ok (s, Access.ownerViolation)

/-- Owner grants `amount` credit to `who` (overwrite, not additive).
    Non-owner → `Unauthorized(caller)`; paused → `Paused()`; zero → `ZeroAddress()`. -/
@[pf_entry]
def grant (s : State) (who : Address) (amount : UInt256) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Access.requireRunning s.paused then
      if Address.isZero who then
        .ok (s, Revert.zeroAddress)
      else
        .ok (s, credits.put who amount)
    else
      .ok (s, Access.runningViolation)
  else
    .ok (s, Access.ownerViolation)

/-- Caller claims `amount` of their own credit into `total`, debiting it. Follows the
    `Examples.Token.burn` shape: a parameter-bound balance gate, the debit read as the
    write's own operand (so the read precedes the write), and `Insufficient(held, wanted)`
    when the credit is short. Paused → `Paused()`. `total` is a UInt256 word: addition
    wraps at 2^256, the same arithmetic contract `Examples.Token` documents for `supply`. -/
@[pf_entry]
def claim (s : State) (amount : UInt256) : Except Error (State × UInt64) :=
  if Access.requireRunning s.paused then
    if credits.containsAtLeast Context.caller amount then
      .ok ({ owner := s.owner, paused := s.paused, total := UInt256.add s.total amount },
        credits.put Context.caller (credits.nextSub Context.caller amount))
    else
      .ok ({ owner := s.owner, paused := s.paused, total := s.total },
        credits.revertInsufficient Context.caller amount)
  else
    .ok (s, Access.runningViolation)

/-- Owner-gated pause. The `0 ≠ 1` guard marks the checked state transition for extraction,
    matching the existing EVM examples. -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if (0 : UInt64) ≠ 1 then
      .ok ({ owner := s.owner, paused := Access.pausedFlag, total := s.total }, 1)
    else
      .error .overflow
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated unpause. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if (0 : UInt64) ≠ 1 then
      .ok ({ owner := s.owner, paused := Access.runningFlag, total := s.total }, 0)
    else
      .error .overflow
  else
    .ok (s, Access.ownerViolation)

@[pf_entry]
def ownerOf (s : State) : Address :=
  s.owner

@[pf_entry]
def creditOf (_s : State) (who : Address) : UInt256 :=
  credits.get who

@[pf_entry]
def pendingOf (_s : State) (who : Address) : UInt64 :=
  ownership.nominationOf who

@[pf_entry]
def totalOf (s : State) : UInt256 :=
  s.total

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

end Examples.Credits
