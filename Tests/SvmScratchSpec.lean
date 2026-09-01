import ProofForge.Svm.Scratch

namespace Tests.SvmScratchSpec

open ProofForge.Svm
open ProofForge.Svm.Scratch

#guard cpiBank.wellFormed
#guard scalarBank.wellFormed
#guard deepBank.wellFormed
#guard cpiBank.lifetime == .invocationOnly
#guard cpiBank.lowWater == 1152
#guard deepBank.lowWater == 2176
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
  tail : SignerSeedTail

private def dynamicSelfPlan (accountCount seedBytes : Nat) :
    Except String DynamicSelfLayout := do
  let instruction ← instructionPlan cpiBank
    { metaCount := 1, dataBytes := 0, accountCount }
  let tail ← instruction.scratch.signerSeedTail seedBytes 1
  return { instruction, tail }

-- Existing BatchRecorder geometry is preserved without emitter-local offsets.
#guard
  match dynamicSelfPlan 4 3 with
  | .ok layout =>
      layout.tail.scratch.frameBytes == 344 && layout.tail.scratch.laidOut &&
        layout.instruction.metas.offset == 0 &&
        layout.instruction.instruction.offset == 16 &&
        layout.instruction.infos.offset == 56 &&
        layout.tail.bytes.offset == 280 && layout.tail.bump.offset == 288 &&
        layout.tail.entries.offset == 296 && layout.tail.bumpEntryOffset == 312 &&
        layout.tail.group.offset == 328
  | .error _ => false

-- The exact account boundary fits; the next account fails before emission.
#guard
  match dynamicSelfPlan 16 3 with
  | .ok layout => layout.tail.scratch.frameBytes == 1016
  | .error _ => false

#guard
  match dynamicSelfPlan 17 3 with
  | .error message => message.contains "requires 1056 bytes" && message.contains "maximum is 1024"
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

-- Ordinary invoke signer-tail guards: exact fit, OOM, mixed seed shapes, and alignment.

-- Exact fit: a 14-account buffer leaves 184 bytes, enough for 5 seeds of 64 copied bytes, the
-- bump byte, 6 entry slots, and the signer group, ending exactly at the 1024-byte boundary.
private def invokeTailPlan (accountCount copiedBytes seedCount : Nat) :
    Except String SignerSeedTail := do
  let instruction ← instructionPlan cpiBank
    { metaCount := 1, dataBytes := 0, accountCount }
  instruction.scratch.signerSeedTail copiedBytes seedCount

#guard
  match invokeTailPlan 14 64 5 with
  | .ok tail =>
      tail.scratch.frameBytes == 1024 && tail.scratch.laidOut &&
        tail.bytes.offset == 840 && tail.bump.offset == 904 &&
        tail.entries.offset == 912 && tail.bumpEntryOffset == 992 &&
        tail.group.offset == 1008
  | .error _ => false

-- One copied byte more leaves the bank and is rejected before emission.
#guard
  match invokeTailPlan 14 65 5 with
  | .error message => message.contains "requires 1032 bytes" && message.contains "maximum is 1024"
  | .ok _ => false

-- An empty copied region with no seeds still reserves only the bump entry and group.
#guard
  match invokeTailPlan 4 0 0 with
  | .ok tail =>
      tail.bytes.offset == 280 && tail.bytes.size == 0 && tail.bump.offset == 280 &&
        tail.entries.offset == 288 && tail.bumpEntryOffset == 288 &&
        tail.group.offset == 304 && tail.scratch.frameBytes == 320 &&
        tail.scratch.laidOut
  | .error _ => false

-- A non-copied multi-seed mix (state/account/data seeds) keeps size-zero copied bytes while
-- every seed still gets one descriptor plus the shared bump entry.
#guard
  match invokeTailPlan 4 0 3 with
  | .ok tail =>
      tail.bytes.offset == 280 && tail.bytes.size == 0 && tail.bump.offset == 280 &&
        tail.entries.offset == 288 && tail.entries.size == 64 &&
        tail.bumpEntryOffset == 336 && tail.group.offset == 352 &&
        tail.scratch.frameBytes == 368 && tail.scratch.laidOut
  | .error _ => false

-- An ascii/non-copied mix keeps the copied region packed and the bump byte 8-aligned even when
-- the copied byte count is not.
#guard
  match invokeTailPlan 4 5 2 with
  | .ok tail =>
      tail.bytes.offset == 280 && tail.bytes.size == 5 && tail.bump.offset == 288 &&
        tail.entries.offset == 296 && tail.bumpEntryOffset == 328 &&
        tail.group.offset == 344 && tail.scratch.frameBytes == 360 &&
        tail.scratch.laidOut
  | .error _ => false

-- A maximal 15-seed group with no copied bytes still overflows the 1024-byte bank.
#guard
  match invokeTailPlan 14 0 15 with
  | .error message => message.contains "requires 1104 bytes" && message.contains "maximum is 1024"
  | .ok _ => false

-- Fixed return-data staging: 32-byte program id, fixed 8-byte payload, exact bank fit, and the
-- established deep-sysvar physical distances.
#guard returnDataBank.wellFormed
#guard returnDataPayloadBytes == 8 && returnDataProgramIdBytes == 32

#guard
  match returnDataStaging with
  | .ok staging =>
      staging.scratch.frameBytes == 40 && staging.scratch.laidOut &&
        staging.programId.offset == 0 && staging.programId.size == 32 &&
        staging.payload.offset == 32 && staging.payload.size == 8 &&
        staging.programId.stackDistance returnDataBank == 3104 &&
        staging.payload.stackDistance returnDataBank == 3072
  | .error _ => false

#guard returnDataBank.lifetime == .invocationOnly

end Tests.SvmScratchSpec
