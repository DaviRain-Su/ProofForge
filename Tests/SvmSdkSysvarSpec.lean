import Examples.Clock
import Examples.Epoch
import Examples.Rent
import Lean
import ProofForge

/-!
R3-014 regression: applications consume sysvars through `Svm.Sdk.Sysvar`, while extraction and
emission retain the existing target-owned Clock, EpochSchedule, and Rent host contracts.
-/

namespace Tests.SvmSdkSysvarSpec

open Lean Elab Command
open ProofForge.Svm.Sdk

#guard Sysvar.Clock.slot == ProofForge.Svm.Runtime.clockSlot
#guard Sysvar.Clock.epoch == ProofForge.Svm.Runtime.clockEpoch
#guard Sysvar.Clock.unixTimestamp == ProofForge.Svm.Runtime.unixTime
#guard Sysvar.EpochSchedule.slotsPerEpoch == ProofForge.Svm.Runtime.slotsPerEpoch
#guard Sysvar.Rent.minimumBalance 16 == ProofForge.Svm.Runtime.rentExemption 16

private def expectSysvarCall (module : Name) (needles : Array String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  for needle in needles do
    unless asm.contains needle do
      throwError s!"{module}: SDK sysvar facade lost target host call {needle}"

elab "#pf_guard_sdk_sysvars" : command => do
  expectSysvarCall `Examples.Clock #["call sol_get_clock_sysvar"]
  expectSysvarCall `Examples.Epoch #["call sol_get_epoch_schedule_sysvar"]
  expectSysvarCall `Examples.Rent #["call sol_get_rent_sysvar"]

#pf_guard_sdk_sysvars

end Tests.SvmSdkSysvarSpec
