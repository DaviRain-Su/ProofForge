import ProofForge.Svm.Solanalib

namespace Tests.SolanalibSpec

open ProofForge.Svm.Solanalib
open _root_.Solanalib.SBPF

private def valueSlot : ProofForge.Svm.IR.Slot := {
  name := "value"
  offset := 8
  width := 8
  abi := "u64-le"
}

#guard
  staticStoreInstruction? valueSlot ==
    some (.st .m64 .br6 (.reg .br1) (BitVec.ofNat 16 104))

#guard
  match evalCheckedArithBody .add 7 5 with
  | .oks regs => evalReg .br4 regs == 12
  | _ => false

#guard
  match evalCheckedArithBody .sub 7 5 with
  | .oks regs => evalReg .br4 regs == 2
  | _ => false

-- Solanalib exposes the machine wrap; ProofForge's preceding checked guard must exclude it.
#guard
  match evalCheckedArithBody .add u64Max 1 with
  | .oks regs => evalReg .br4 regs == 0
  | _ => false

#guard
  let regs :=
    setReg (setReg initRegMap .br6 mmInputStart) .br1
      0x0123456789abcdef
  match evalStaticStore? valueSlot regs initMem with
  | some memory =>
      loadv .m64 memory (mmInputStart + 104) ==
        some (.vlong 0x0123456789abcdef)
  | none => false

#guard (staticStoreInstruction? { valueSlot with width := 3 }).isNone

#guard
  (staticStoreInstruction? { valueSlot with offset := 2 ^ 15 }).isNone

end Tests.SolanalibSpec
