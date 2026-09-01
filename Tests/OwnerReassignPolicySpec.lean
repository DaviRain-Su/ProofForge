import Lean
import ProofForge

/-!
`svm-sdk-002` permanent fail-closed policy checks.

Owner reassignment of a live program-owned account is intentionally unavailable. Lifecycle exit
is `Account.Handle.closeTo`; inbound System assign remains system-owned → current program only.
-/
namespace Tests.OwnerReassignPolicySpec

open Lean Elab Command
open ProofForge.Svm.Sdk

-- Policy marker: no `Handle.reassignOwner` surface is part of the SDK.
def ownerReassignFacadeAvailable : Bool := false

#guard ownerReassignFacadeAvailable == false

-- Inbound System assign exists; it is not a program-owned reassignment API.
#guard System.assign == 0

-- The supported program-owned lifecycle exit remains close/refund composition.
#guard (Account.Handle.at 1).closeTo (Account.Handle.at 2) == 0

elab "#pf_guard_owner_reassign_policy" : command => do
  let env ← getEnv
  -- Reject any accidental introduction of a reassignment facade name in the Account SDK module.
  let accountHandle := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr .anonymous
    "ProofForge") "Svm") "Sdk") "Account") "Handle"
  let forbidden := ["reassignOwner", "setOwner", "assignOwner"].map (Name.mkStr accountHandle)
  for name in forbidden do
    if (env.find? name).isSome then
      throwError s!"svm-sdk-002 policy violation: unexpected owner-reassign facade {name}"
  let closeTo := Name.mkStr accountHandle "closeTo"
  unless (env.find? closeTo).isSome do
    throwError "missing Handle.closeTo lifecycle exit"
  let systemAssign := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr .anonymous
    "ProofForge") "Svm") "Sdk") "System") "assign"
  unless (env.find? systemAssign).isSome do
    throwError "missing System.assign inbound acquisition"

#pf_guard_owner_reassign_policy

end Tests.OwnerReassignPolicySpec
