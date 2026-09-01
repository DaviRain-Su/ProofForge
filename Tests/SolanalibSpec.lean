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

private def branchFragment (cmp : ProofForge.Core.Ops.Cmp) : CFGBranchFragment := {
  cmp
  lhs := .lit 0
  rhs := .lit 0
  thenTarget := 21
  elseTarget := 22
  body := branchBody cmp
}

private def branchSelects (cmp : ProofForge.Core.Ops.Cmp) (lhs rhs : U64)
    (expectThen : Bool) : Bool :=
  match evalCFGBranch (branchFragment cmp) lhs rhs initMem with
  | some (.thenEdge target memory) =>
      expectThen && target == 21 && loadv .m64 memory (mmInputStart + 104) == none
  | some (.elseEdge target memory) =>
      !expectThen && target == 22 && loadv .m64 memory (mmInputStart + 104) == none
  | none => false

#guard branchSelects .eq 5 5 true
#guard branchSelects .eq 5 4 false
#guard branchSelects .ne 5 4 true
#guard branchSelects .ne 5 5 false
#guard branchSelects .lt 4 5 true
#guard branchSelects .lt 5 4 false
#guard branchSelects .le 5 5 true
#guard branchSelects .le 6 5 false
#guard branchSelects .gt 5 4 true
#guard branchSelects .gt 4 5 false
#guard branchSelects .ge 5 5 true
#guard branchSelects .ge 4 5 false

#guard (staticStoreInstruction? { valueSlot with width := 3 }).isNone

#guard
  (staticStoreInstruction? { valueSlot with offset := 2 ^ 15 }).isNone

-- E1: Counter-shaped operand materialization + straightline (`svm-sem-001`)
#guard (materializeOperand? (.field counterValueOffset) lhsStackOffset).isSome
#guard (materializeOperand? (.arg counterArg0Offset) rhsStackOffset).isSome
#guard (materializeOperand? (.lit 5) rhsStackOffset).isSome

#guard
  match staticStoreInstruction? valueSlot with
  | some store =>
      (checkedStraightlineFragment? .add 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset)).isSome &&
      (checkedStraightlineFragment? .add 11 12 store
        (.field counterValueOffset) (.lit 5)).isSome
  | none => false

#guard
  match counterInputMem 7 5, staticStoreInstruction? valueSlot with
  | some mem, some store =>
      match evalCounterStraightline .add 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset) mem with
      | some (.success target finalMem) =>
          target == 11 &&
            loadv .m64 finalMem (mmInputStart + 104) == some (.vlong 12)
      | _ => false
  | _, _ => false

#guard
  match counterInputMem (~~~(0 : U64)) 1, staticStoreInstruction? valueSlot with
  | some mem, some store =>
      let before := loadv .m64 mem (mmInputStart + 104)
      match evalCounterStraightline .add 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset) mem with
      | some (.overflow target finalMem) =>
          target == 12 && loadv .m64 finalMem (mmInputStart + 104) == before
      | _ => false
  | _, _ => false

-- E3: Counter increment multi-block CFG (`svm-sem-003`)
#guard
  match staticStoreInstruction? valueSlot with
  | some store =>
      match counterIncrementCFG? 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset) with
      | some cfg =>
          cfg.entry.length + cfg.successBlock.length + cfg.overflowBlock.length ≤
            counterIncrementInstrBound &&
            counterIncrementBlockBound == 3
      | none => false
  | none => false

#guard
  match counterInputMem 7 5, staticStoreInstruction? valueSlot with
  | some mem, some store =>
      match evalCounterIncrementCFG 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset) mem with
      | some (.success target finalMem r0) =>
          target == 11 && r0 == 0 &&
            loadv .m64 finalMem (mmInputStart + 104) == some (.vlong 12)
      | _ => false
  | _, _ => false

#guard
  match counterInputMem (~~~(0 : U64)) 1, staticStoreInstruction? valueSlot with
  | some mem, some store =>
      let before := loadv .m64 mem (mmInputStart + 104)
      match evalCounterIncrementCFG 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset) mem with
      | some (.overflow target finalMem r0) =>
          target == 12 && r0 == BitVec.ofNat 64 overflowReturnCode.toNat &&
            loadv .m64 finalMem (mmInputStart + 104) == before
      | _ => false
  | _, _ => false


-- E4: AccountWords ↔ typed storev/loadv (`svm-sem-004`)
#guard accountWordByteOffset counterValueWord == counterValueOffset
#guard counterValueOffset == 104
#guard counterValueFieldWord? == some counterValueWord
#guard accountWordInStaticRange counterValueWord
#guard !accountWordInStaticRange 4084

#guard
  match storeAccountWord? initMem counterValueWord 42 with
  | some mem => loadAccountWord? mem counterValueWord == some 42
  | none => false

#guard (loadAccountWord? initMem counterValueWord).isNone

#guard
  match projectFieldWrite? (fun _ => 0) counterValueField 0 (accountWordOfU64 42) with
  | some mem => loadAccountWord? mem counterValueWord == some 42
  | none => false

#guard (projectFieldWrite? (fun _ => 0) counterValueField 1 (accountWordOfU64 7)).isNone

#guard
  let regs := setReg (setReg initRegMap .br6 mmInputStart) .br1 42
  match evalStaticStore? valueSlot regs initMem,
        storeAccountWord? initMem counterValueWord 42 with
  | some a, some b =>
      loadAccountWord? a counterValueWord == some 42 &&
        loadAccountWord? b counterValueWord == some 42
  | _, _ => false

end Tests.SolanalibSpec
