import Examples.Clock
import Examples.Epoch
import Examples.Rent
import Lean
import ProofForge

/-!
Applications consume sysvars through `Svm.Sdk.Sysvar`; extraction routes the target-owned Clock,
EpochSchedule, and Rent host contracts through the generic Component query bridge.
-/

namespace Tests.SvmSdkSysvarSpec

open Lean Elab Command
open ProofForge.Svm.Sdk

#guard Sysvar.Clock.slot == ProofForge.Svm.Runtime.clockSlot
#guard Sysvar.Clock.epoch == ProofForge.Svm.Runtime.clockEpoch
#guard Sysvar.Clock.unixTimestamp == ProofForge.Svm.Runtime.unixTime
#guard Sysvar.EpochSchedule.slotsPerEpoch == ProofForge.Svm.Runtime.slotsPerEpoch
#guard Sysvar.Rent.minimumBalance 16 == ProofForge.Svm.Runtime.rentExemption 16
#guard (ProofForge.Svm.Sysvar.Query.clock .slot).wellFormed
#guard
  (ProofForge.Svm.Sysvar.Query.clock .slot).canonical (fun _ : UInt64 => "v") #[] == "clk"
#guard
  (ProofForge.Svm.Sysvar.Query.rentExemption 16).canonical (fun _ : UInt64 => "v") #[] ==
    "rent.16"

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
  let hasComponentQuery := program.methods.any fun method => method.ops.any fun
    | .returnU64 (.ext (.component (.sysvar _)) #[]) => true
    | .storeField _ (.ext (.component (.sysvar _)) #[]) => true
    | _ => false
  unless hasComponentQuery do
    throwError s!"{module}: sysvar read escaped the generic component bridge"
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
