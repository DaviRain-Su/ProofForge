import ProofForge

/-!
Owner-managed UInt128 consumer of the shared `Core.SafeCast` policy. Unlike the permissionless
accumulator, this application applies authorization first, rejects zero values with independent
application errors, and replaces rather than adds to UInt64, UInt32, UInt16, and UInt8 state
fields.
-/

namespace Examples.Evm.EvmSafeCastConfig
open ProofForge.Core
open ProofForge.Core.Value
open ProofForge.Evm.Sdk

structure State where
  admin : Address
  limit : UInt64
  window : UInt32
  threshold : UInt16
  level : UInt8
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | invalidLimit
  | zero
  | invalidWindow
  | windowZero
  | invalidThreshold
  | thresholdZero
  | invalidLevel
  | levelZero
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (admin : Address) : State :=
  { admin, limit := 7, window := 3, threshold := 5, level := 6 }

@[pf_entry]
def adminOf (s : State) : Address :=
  s.admin

@[pf_entry]
def limitOf (s : State) : UInt64 :=
  s.limit

@[pf_entry]
def windowOf (s : State) : UInt32 :=
  s.window

@[pf_entry]
def thresholdOf (s : State) : UInt16 :=
  s.threshold

@[pf_entry]
def levelOf (s : State) : UInt8 :=
  s.level

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

/-- Owner-gated UInt128→UInt16 replacement. Authorization and every discarded-bit check precede
the only `threshold` state update. -/
@[pf_entry]
def setThreshold (s : State) (value : UInt128) : Except Error (State × UInt16) :=
  if Access.requireOwner s.admin then
    do
      let threshold ← SafeCast.UInt128.toUInt16 value .invalidThreshold
      if threshold == 0 then
        .error .thresholdZero
      else
        .ok ({ s with threshold }, threshold)
  else
    .ok (s, Access.ownerViolation.toUInt16)

/-- Owner-gated UInt128→UInt8 replacement. The result widens back to UInt64 so the unauthorized
branch preserves the SDK's full owner-violation sentinel instead of truncating it to one byte. -/
@[pf_entry]
def setLevel (s : State) (value : UInt128) : Except Error (State × UInt64) :=
  if Access.requireOwner s.admin then
    do
      let level ← SafeCast.UInt128.toUInt8 value .invalidLevel
      if level == 0 then
        .error .levelZero
      else
        .ok ({ s with level }, level.toUInt64)
  else
    .ok (s, Access.ownerViolation)

end Examples.Evm.EvmSafeCastConfig