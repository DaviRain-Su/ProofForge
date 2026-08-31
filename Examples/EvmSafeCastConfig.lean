import ProofForge

/-!
Owner-managed UInt128 consumer of the shared `Core.SafeCast` policy. Unlike the permissionless
accumulator, this application applies authorization first, rejects zero limits with an
application-specific error, and replaces rather than adds to one scalar state field.
-/

namespace Examples.EvmSafeCastConfig

open ProofForge.Core
open ProofForge.Core.Value
open ProofForge.Evm.Sdk

structure State where
  admin : Address
  limit : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | invalidLimit
  | zero
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, limit := 7 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def limitOf (s : State) : UInt64 :=
  s.limit

/-- Owner-gated UInt128→UInt64 replacement. Authorization and both validation decisions precede
the only state update. -/
@[pf_entry]
def setLimit (s : State) (value : UInt128) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    do
      let limit ← SafeCast.UInt128.toUInt64 value .invalidLimit
      if limit == 0 then
        .error .zero
      else
        .ok ({ s with limit }, limit)
  else
    .ok (s, Access.ownerViolation)

end Examples.EvmSafeCastConfig
