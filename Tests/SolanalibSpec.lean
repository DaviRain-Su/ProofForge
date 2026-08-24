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

#guard checkedArithGuard .add 7 5
#guard !checkedArithGuard .add u64Max 1
#guard checkedArithGuard .sub 7 5
#guard !checkedArithGuard .sub 5 7
#guard checkedArithGuard .mul 7 5
#guard checkedArithGuard .mul u64Max 0
#guard !checkedArithGuard .mul u64Max 2
#guard checkedArithGuard .div 7 5
#guard !checkedArithGuard .div 7 0
#guard checkedArithGuard .mod 7 5
#guard !checkedArithGuard .mod 7 0

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

#guard
  match evalCheckedWrite? valueSlot .add 7 5 initMem with
  | some memory =>
      loadv .m64 memory (mmInputStart + 104) == some (.vlong 12)
  | none => false

#guard (evalCheckedWrite? valueSlot .add u64Max 1 initMem).isNone

private def checkedControl (kind : ProofForge.Core.CheckedArith) :=
  checkedControlFragment kind 11 12
    (.st .m64 .br6 (.reg .br1) (BitVec.ofNat 16 104))

private def checkedSucceedsWith (kind : ProofForge.Core.CheckedArith)
    (lhs rhs expected : U64) : Bool :=
  match evalCheckedCFGWrite (checkedControl kind) lhs rhs initMem with
  | some (.success target memory) =>
      target == 11 &&
        loadv .m64 memory (mmInputStart + 104) == some (.vlong expected)
  | _ => false

private def checkedOverflowsWithoutWrite (kind : ProofForge.Core.CheckedArith)
    (lhs rhs : U64) : Bool :=
  match evalCheckedCFGWrite (checkedControl kind) lhs rhs initMem with
  | some (.overflow target memory) =>
      target == 12 && loadv .m64 memory (mmInputStart + 104) == none
  | _ => false

#guard checkedSucceedsWith .add 7 5 12
#guard checkedSucceedsWith .sub 7 5 2
#guard checkedSucceedsWith .mul 7 5 35
#guard checkedSucceedsWith .mul u64Max 0 0
#guard checkedSucceedsWith .div 7 5 1
#guard checkedSucceedsWith .mod 7 5 2

-- Every typed conditional guard selects overflow before either scratch or state store.
#guard checkedOverflowsWithoutWrite .add u64Max 1
#guard checkedOverflowsWithoutWrite .sub 5 7
#guard checkedOverflowsWithoutWrite .mul u64Max 2
#guard checkedOverflowsWithoutWrite .div 7 0
#guard checkedOverflowsWithoutWrite .mod 7 0

#guard (staticStoreInstruction? { valueSlot with width := 3 }).isNone

#guard
  (staticStoreInstruction? { valueSlot with offset := 2 ^ 15 }).isNone

end Tests.SolanalibSpec
