import ProofForge.Svm.BatchRecorder
import ProofForge.Svm.Cpi.Emit
import ProofForge.Svm.FifoCancel
import ProofForge.Svm.Heap.Emit
import ProofForge.Svm.Sdk.Transient
import ProofForge.Svm.Transient.Emit
import ProofForge.Svm.TransientBytes
import ProofForge.Svm.TransientVec

namespace Tests.SvmTransientSpec

open ProofForge.Svm
open ProofForge.Svm.Sdk.Transient

#guard Scratch.cpiBank.lifetime == Scratch.Lifetime.invocationOnly

private def recorderBuffer : HeapBuffer :=
  { name := "recorder", capacityBytes := BatchRecorder.maxInnerDataBytes }

#guard recorderBuffer.wellFormed
#guard recorderBuffer.minimumFrame == some Heap.defaultFrameBytes
#guard
  match recorderBuffer.reserveFresh with
  | .ok reservation =>
      reservation.allocation.size == BatchRecorder.maxInnerDataBytes &&
        reservation.allocation.pointer % 8 == 0 && reservation.heap.wellFormed
  | .error _ => false

private def wholeFrame : HeapBuffer :=
  { name := "whole", capacityBytes := Heap.defaultFrameBytes - Heap.bumpWordBytes }

#guard wholeFrame.wellFormed
#guard
  match wholeFrame.reserveFresh with
  | .ok reservation =>
      reservation.allocation.pointer == Heap.usableStart &&
        match ({ name := "one-more", capacityBytes := 1, alignment := 1 } : HeapBuffer).reserve
            reservation.heap with
        | .error message => message.contains "out of memory"
        | .ok _ => false
  | .error _ => false

#guard
  match ({ name := "zero", capacityBytes := 0 } : HeapBuffer).reserveFresh with
  | .error message => message.contains "malformed"
  | .ok _ => false

#guard
  match ({ name := "unaligned", capacityBytes := 64, alignment := 3 } : HeapBuffer).reserveFresh with
  | .error message => message.contains "malformed"
  | .ok _ => false

private def words : FixedVec :=
  { buffer := { name := "words", capacityBytes := 128 }, elementBytes := 8, capacity := 16 }

#guard words.wellFormed
#guard words.indexFits 15
#guard !words.indexFits 16
#guard
  !({ words with buffer := { words.buffer with capacityBytes := 127 } }).wellFormed

private def vector2 : TransientVec.Config := { capacity := 2 }
private def vectorMax : TransientVec.Config := { capacity := 4095 }
private def vector2B : TransientVec.Config :=
  { capacity := secondSlotWord 2 }

#guard vector2.wellFormed
#guard vector2.fixedVec.buffer.capacityBytes == 16
#guard vectorMax.wellFormed
#guard !({ capacity := 4096 } : TransientVec.Config).wellFormed

-- The reusable handle identity: slot 0 keeps the plain-payload word; slot 1 packs itself above
-- bit 32. A third slot and a zero payload are malformed in the same reusable contract.
#guard vector2.slot == 0 && vector2.payload == 2
#guard vector2B.wellFormed
#guard vector2B.slot == 1 && vector2B.payload == 2
#guard vector2B.fixedVec == vector2.fixedVec
#guard vector2 != vector2B
#guard (TransientVec.Call.begin vector2 : TransientVec.Call UInt64).canonical toString !=
  (TransientVec.Call.begin vector2B : TransientVec.Call UInt64).canonical toString
#guard
  !({ capacity := 2 * handleSlotBit } : TransientVec.Config).wellFormed
#guard
  !({ capacity := handleSlotBit } : TransientVec.Config).wellFormed
#guard TransientVec.pointerStack > FifoCancel.queryScratchEnd
#guard TransientVec.activeStack < Scratch.returnDataBank.lowWater
-- Same-kind slot banks are disjoint: slot 1 starts exactly one slotStride above slot 0 and ends
-- before the byte-buffer bank.
#guard TransientVec.pointerStack + ProofForge.Svm.Transient.Emit.slotStride ≤ TransientBytes.pointerStack
#guard TransientVec.activeStack + ProofForge.Svm.Transient.Emit.slotStride + 8 ≤
  TransientBytes.pointerStack
-- The byte-kind slot banks stay below the shared `sol_log_data` descriptor and the deep
-- account-storage scratch.
#guard TransientBytes.pointerStack + ProofForge.Svm.Transient.Emit.slotStride + 24 ≤
  TransientBytes.descriptorStack - 16
#guard TransientBytes.descriptorStack ≤ 2488
#guard TransientVec.oomErrorCode != TransientVec.boundsErrorCode
#guard TransientVec.boundsErrorCode != TransientVec.stateErrorCode

#guard
  match Heap.Emit.emitAllocate "recorder" "fixture" 16 8 416
      "  lddw r0, 0x1\n  exit\n" with
  | .ok asm =>
      asm.contains "recorder_heap_position_fixture" &&
        asm.contains "lddw r3, 0xfffffffffffffff8" &&
        asm.contains "stxdw [r10 - 416], r2"
  | .error _ => false

private def recorderConfig : BatchRecorder.Config :=
  { logAccount := 1, selfEntryTag := 42, authoritySeed := "pf", maxBytes := 1246,
    headerBytes := 16, countOffset := 0, maxRecords := 64 }

#guard recorderConfig.wellFormed
#guard recorderConfig.transientWriter.wellFormed
#guard recorderConfig.transientWriter.buffer.capacityBytes == BatchRecorder.maxInnerDataBytes
#guard recorderConfig.transientWriter.recordFits 16 63 1230
#guard recorderConfig.transientWriter.flushRequired 16 63 1231
#guard recorderConfig.transientWriter.flushRequired 16 64 1
#guard !recorderConfig.transientWriter.recordFits 16 0 0
#guard
  let malformed := { recorderConfig with countOffset := 15 }
  !malformed.wellFormed && !malformed.transientWriter.wellFormed

private def signedCpi (accountCount seedBytes seedCount : Nat) :
    Except String SignedCpiCodec :=
  SignedCpiCodec.plan Scratch.cpiBank
    { metaCount := 1, dataBytes := 0, accountCount } seedBytes seedCount

#guard
  match signedCpi 4 3 1 with
  | .ok codec =>
      codec.signer.scratch.frameBytes == 344 &&
        (codec.signer.scratch.region? "metas").map (·.offset) == some 0 &&
        (codec.signer.scratch.region? "instruction").map (·.offset) == some 16 &&
        (codec.signer.scratch.region? "infos").map (·.offset) == some 56 &&
        codec.signer.bytes.offset == 280 && codec.signer.bump.offset == 288 &&
        codec.signer.entries.offset == 296 && codec.signer.group.offset == 328
  | .error _ => false

#guard
  match signedCpi 16 3 1 with
  | .ok codec => codec.signer.scratch.frameBytes == 1016
  | .error _ => false

#guard
  match signedCpi 17 3 1 with
  | .error message => message.contains "requires 1056 bytes" && message.contains "maximum is 1024"
  | .ok _ => false

#guard
  match SignedCpiCodec.plan { Scratch.cpiBank with name := "" }
      { metaCount := 1, dataBytes := 0, accountCount := 1 } 3 1 with
  | .error message => message.contains "malformed"
  | .ok _ => false

end Tests.SvmTransientSpec
