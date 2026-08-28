import ProofForge.Svm.Scratch

namespace Tests.SvmScratchSpec

open ProofForge.Svm
open ProofForge.Svm.Scratch

#guard cpiBank.wellFormed
#guard scalarBank.wellFormed
#guard deepBank.wellFormed
#guard cpiBank.lifetime == .invocationOnly
#guard cpiBank.lowWater == 1024
#guard deepBank.lowWater == 2048
#guard Bank.disjoint cpiBank scalarBank
#guard Bank.disjoint deepBank cpiBank
#guard !Bank.disjoint cpiBank cpiBank

#guard Heap.alignUp 0 8 == 0
#guard Heap.alignUp 1 8 == 8
#guard Heap.alignUp 283 8 == 288
#guard Heap.alignUp 5 3 == 5

-- Malformed physical geometry is rejected before any region can be formed.
#guard
  match Plan.open { cpiBank with name := "" } with
  | .error message => message.contains "malformed"
  | .ok _ => false

#guard
  match Plan.open { cpiBank with capacityBytes := 4096 } with
  | .error message => message.contains "malformed"
  | .ok _ => false

private def oneRegion (name : String) (size alignment : Nat) : Except String Allocation := do
  let plan ← Plan.open cpiBank
  plan.alloc name size alignment

#guard
  match oneRegion "exact" 1024 8 with
  | .ok allocation => allocation.plan.frameBytes == 1024 && allocation.plan.laidOut
  | .error _ => false

#guard
  match oneRegion "over" 1025 8 with
  | .error message => message.contains "requires 1025 bytes" && message.contains "maximum is 1024"
  | .ok _ => false

#guard
  match oneRegion "unaligned" 8 3 with
  | .error message => message.contains "invalid alignment 3"
  | .ok _ => false

#guard
  match oneRegion "" 8 8 with
  | .error message => message.contains "empty name"
  | .ok _ => false

#guard
  match oneRegion "same" 8 8 with
  | .ok first =>
      match first.plan.alloc "same" 8 8 with
      | .error message => message.contains "duplicated"
      | .ok _ => false
  | .error _ => false

structure DynamicSelfLayout where
  instruction : InstructionPlan
  scratch : Plan
  seed : Region
  bump : Region
  seedEntries : Region
  bumpEntry : Region
  signerGroup : Region

private def dynamicSelfPlan (accountCount seedBytes : Nat) : Except String DynamicSelfLayout := do
  let instruction ← instructionPlan cpiBank
    { metaCount := 1, dataBytes := 0, accountCount }
  let seed ← instruction.scratch.alloc "seed" seedBytes 1
  let bump ← seed.plan.alloc "bump" 1 8
  let seedEntries ← bump.plan.alloc "seedEntries" 16 8
  let bumpEntry ← seedEntries.plan.alloc "bumpEntry" 16 8
  let signerGroup ← bumpEntry.plan.alloc "signerGroup" 16 8
  return {
    instruction
    scratch := signerGroup.plan
    seed := seed.region
    bump := bump.region
    seedEntries := seedEntries.region
    bumpEntry := bumpEntry.region
    signerGroup := signerGroup.region
  }

-- Existing BatchRecorder geometry is preserved without emitter-local offsets.
#guard
  match dynamicSelfPlan 4 3 with
  | .ok layout =>
      layout.scratch.frameBytes == 344 && layout.scratch.laidOut &&
        layout.instruction.metas.offset == 0 &&
        layout.instruction.instruction.offset == 16 &&
        layout.instruction.infos.offset == 56 &&
        layout.seed.offset == 280 && layout.bump.offset == 288 &&
        layout.seedEntries.offset == 296 && layout.bumpEntry.offset == 312 &&
        layout.signerGroup.offset == 328
  | .error _ => false

-- The exact account boundary fits; the next account fails before emission.
#guard
  match dynamicSelfPlan 16 3 with
  | .ok layout => layout.scratch.frameBytes == 1016
  | .error _ => false

#guard
  match dynamicSelfPlan 17 3 with
  | .error message => message.contains "requires 1040 bytes" && message.contains "maximum is 1024"
  | .ok _ => false

#guard
  let buffer : InstructionBuffer := { metaCount := 2, dataBytes := 57, accountCount := 3 }
  buffer.metaBytes == 32 && buffer.instructionOffset == 32 &&
    buffer.dataOffset == 72 && buffer.dataSpan == 64 &&
    buffer.infoOffset == 136 && buffer.infoBytes == 168 && buffer.seedOffset == 304

#guard
  match instructionPlan cpiBank { metaCount := 2, dataBytes := 57, accountCount := 3 } with
  | .ok plan =>
      plan.metas.offset == 0 && plan.instruction.offset == 32 &&
        plan.data.offset == 72 && plan.infos.offset == 136 &&
        plan.scratch.frameBytes == 304 && plan.scratch.laidOut
  | .error _ => false

#guard
  match instructionPlan cpiBank { metaCount := 4, dataBytes := 64, accountCount := 64 } with
  | .error message => message.contains "maximum is 1024"
  | .ok _ => false

end Tests.SvmScratchSpec
