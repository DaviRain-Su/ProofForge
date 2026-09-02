import Examples.Svm.Clock
import Examples.Svm.Epoch
import Examples.Svm.Rent
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
#guard Sysvar.Clock.epochStartTimestamp == ProofForge.Svm.Runtime.clockEpochStartTimestamp
#guard Sysvar.Clock.leaderScheduleEpoch == ProofForge.Svm.Runtime.clockLeaderScheduleEpoch
#guard Sysvar.Clock.unixTimestamp == ProofForge.Svm.Runtime.unixTime
#guard Sysvar.Clock.asSigned (UInt64.ofNat 0) == (0 : Int)
#guard Sysvar.Clock.asSigned (UInt64.ofNat 1) == (1 : Int)
#guard Sysvar.Clock.asSigned (~~~(0 : UInt64)) == (-1 : Int)
#guard Sysvar.Clock.asSigned (UInt64.ofNat 0xFFFFFFFFFFFFFFFF) == (-1 : Int)
#guard Sysvar.EpochSchedule.slotsPerEpoch == ProofForge.Svm.Runtime.slotsPerEpoch
#guard
  Sysvar.EpochSchedule.leaderScheduleSlotOffset ==
    ProofForge.Svm.Runtime.epochScheduleLeaderScheduleSlotOffset
#guard Sysvar.EpochSchedule.warmup == (ProofForge.Svm.Runtime.epochScheduleWarmup != 0)
#guard
  Sysvar.EpochSchedule.firstNormalEpoch ==
    ProofForge.Svm.Runtime.epochScheduleFirstNormalEpoch
#guard
  Sysvar.EpochSchedule.firstNormalSlot == ProofForge.Svm.Runtime.epochScheduleFirstNormalSlot
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
  expectSysvarCall `Examples.Svm.Clock #["call sol_get_clock_sysvar",
    "load clock.leaderScheduleEpoch", "ldxdw r1, [r10 - 3048]",
    "load clock.epochStartTimestamp", "ldxdw r1, [r10 - 3064]",
    "load clock.unix", "ldxdw r1, [r10 - 3040]"]
  expectSysvarCall `Examples.Svm.Epoch #["call sol_get_epoch_schedule_sysvar",
    "load leaderScheduleSlotOffset", "ldxdw r1, [r10 - 3064]", "load warmup",
    "ldxb r1, [r10 - 3056]", "load firstNormalEpoch", "ldxdw r1, [r10 - 3048]",
    "load firstNormalSlot", "ldxdw r1, [r10 - 3040]"]
  expectSysvarCall `Examples.Svm.Rent #["call sol_get_rent_sysvar"]

#pf_guard_sdk_sysvars

end Tests.SvmSdkSysvarSpec
