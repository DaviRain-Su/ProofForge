import ProofForge

namespace Examples.Credits

open ProofForge.Evm.Sdk

/-!
EVM-SDK-1 consumer B (independent of `Examples.TwoStepCounter`): an owner-granted credit
ledger. Reuses the same `Access` gates and fixed single-pending `Access.Ownership` value,
plus one typed hashed-map namespace for per-account credits.

State: stored `owner` (rotated by two-step transfer), explicit `paused` flag, `UInt256` `total` of
claimed credits, and one fixed pending owner. `credits` uses namespace 0 of `AddressMap256`, the map
shape whose get/condition/put binding `Examples.Token` already proves end to end. All storage writes
stay in this file.
-/

structure State where
  owner : Address
  paused : UInt8
  total : UInt256
  ownership : Address
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def credits : Storage.AddressMap256 :=
  Storage.Layout.root.addressMap256.handle

@[pf_entry]
def init (owner : Address) : State :=
  { owner, paused := Access.runningFlag, total := UInt256.zero,
    ownership := Access.Ownership.none }

/-- Owner nominates `candidate` for the two-step transfer. -/
@[pf_entry]
def transferOwnership (s : State) (candidate : Address) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if Address.isZero candidate then
      .ok (s, Revert.zeroAddress)
    else
      .ok ({ s with ownership := Access.Ownership.nominate s.ownership candidate }, 1)
  else
    .ok (s, Access.ownerViolation)

/-- Nominee accepts; the owner-field write is explicit here. -/
@[pf_entry]
def acceptOwnership (s : State) : Except Error (State × UInt64) :=
  if Access.Ownership.callerIsPending s.ownership then
    .ok ({ owner := Context.caller, paused := s.paused, total := s.total, ownership :=
      Access.Ownership.consume s.ownership }, 1)
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
      .ok ({ s with total := UInt256.add s.total amount },
        credits.put Context.caller (credits.nextSub Context.caller amount))
    else
      .ok (s, credits.revertInsufficient Context.caller amount)
  else
    .ok (s, Access.runningViolation)

/-- Owner-gated pause. -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    .ok ({ s with paused := Access.pausedFlag }, 1)
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated unpause. -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    .ok ({ s with paused := Access.runningFlag }, 0)
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
  Access.Ownership.nominationOf _s.ownership who

@[pf_entry]
def totalOf (s : State) : UInt256 :=
  s.total

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

end Examples.Credits
