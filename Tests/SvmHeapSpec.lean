import ProofForge.Svm.Heap

namespace Tests.SvmHeapSpec

open ProofForge.Svm.Heap

#guard startAddress == 0x300000000
#guard defaultFrameBytes == 32768
#guard maxFrameBytes == 262144
#guard alignOfU128 == 8

#guard frameSizeValid defaultFrameBytes
#guard frameSizeValid (33 * 1024)
#guard frameSizeValid maxFrameBytes
#guard !frameSizeValid (defaultFrameBytes - 1)
#guard !frameSizeValid (maxFrameBytes + 1024)
#guard !frameSizeValid (defaultFrameBytes + 1)

#guard alignmentValid 1
#guard alignmentValid 8
#guard alignmentValid 4096
#guard !alignmentValid 0
#guard !alignmentValid 3

#guard (initial defaultFrameBytes).wellFormed
#guard !(initial (31 * 1024)).wellFormed
#guard !({ frameBytes := defaultFrameBytes, bump := startAddress } : State).wellFormed

#guard
  match allocate (initial defaultFrameBytes) 8 8 with
  | some (allocation, state) =>
      allocation.pointer == startAddress + defaultFrameBytes - 8 &&
        state.bump == allocation.pointer && state.wellFormed
  | none => false

#guard
  match allocate (initial defaultFrameBytes) 8 8 with
  | some (_, first) =>
      match allocate first 1 16 with
      | some (allocation, second) =>
          allocation.pointer == startAddress + defaultFrameBytes - 16 &&
            allocation.pointer % 16 == 0 && second.bump == allocation.pointer
      | none => false
  | none => false

#guard
  match allocate (initial defaultFrameBytes) (defaultFrameBytes - bumpWordBytes) 1 with
  | some (allocation, full) =>
      allocation.pointer == usableStart && allocate full 1 1 == none
  | none => false

#guard allocate (initial defaultFrameBytes) defaultFrameBytes 1 == none
#guard allocate (initial defaultFrameBytes) 8 3 == none

#guard
  match allocate (initial defaultFrameBytes) 32 alignOfU128 with
  | some (allocation, state) => deallocate state allocation == state
  | none => false

end Tests.SvmHeapSpec
