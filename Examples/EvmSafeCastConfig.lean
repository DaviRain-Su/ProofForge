import ProofForge

/-!
Owner-managed UInt128 consumer of the shared `Core.SafeCast` policy. Unlike the permissionless
accumulator, this application applies authorization first, rejects zero values with independent
application errors, and replaces rather than adds to UInt64 and UInt32 state fields.
-/

namespace Examples.EvmSafeCastConfig

open ProofForge.Core
open ProofForge.Core.Value
open ProofForge.Evm.Sdk

structure State where
  admin : Address
  limit : UInt64
  window : UInt32
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | invalidLimit
  | zero
  | invalidWindow
  | windowZero
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, limit := 7, window := 3 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def limitOf (s : State) : UInt64 :=
  s.limit

@[pf_entry]
def windowOf (s : State) : UInt32 :=
  s.window

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

/-- Owner-gated UInt128→UInt32 replacement. The caller and every discarded bit are checked before
the only `window` state update. -/
@[pf_entry]
def setWindow (s : State) (value : UInt128) : Except Error (State × UInt32) :=
  if Access.requireOwner s.admin then
    do
      let window ← SafeCast.UInt128.toUInt32 value .invalidWindow
      if window == 0 then
        .error .windowZero
      else
        .ok ({ s with window }, window)
  else
    .ok (s, Access.ownerViolation.toUInt32)

end Examples.EvmSafeCastConfig
