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


-- E5: BoundedQueue empty-push L3 (`svm-sem-005`)
#guard demoQueue.wellFormed
#guard demoQueueHeadWord? == some demoQueueHeadWord
#guard demoQueueCountWord? == some demoQueueCountWord
#guard demoQueueSlot1Word? == some demoQueueSlot1Word
#guard accountWordInStaticRange demoQueueHeadWord
#guard accountWordInStaticRange demoQueueCountWord
#guard accountWordInStaticRange demoQueueSlot1Word

#guard
  demoEmptyPushCount (accountWordOfU64 42) == 1 &&
    demoEmptyPushHead (accountWordOfU64 42) == 1 &&
      demoEmptyPushSlot1 (accountWordOfU64 42) == accountWordOfU64 42

#guard
  match projectDemoEmptyPush? 42 with
  | some mem =>
      loadAccountWord? mem demoQueueSlot1Word == some 42 &&
        loadAccountWord? mem demoQueueHeadWord == some 1 &&
          loadAccountWord? mem demoQueueCountWord == some 1
  | none => false

#guard
  match demoEmptyPushStores? 42, projectDemoEmptyPush? 42 with
  | some a, some b =>
      loadAccountWord? a demoQueueSlot1Word == loadAccountWord? b demoQueueSlot1Word &&
        loadAccountWord? a demoQueueHeadWord == loadAccountWord? b demoQueueHeadWord &&
          loadAccountWord? a demoQueueCountWord == loadAccountWord? b demoQueueCountWord
  | _, _ => false


-- E∞: walked r7 instruction-data cursor (`svm-sem-006`)
#guard (walkArgU64? rhsStackOffset).isSome
#guard
  match (do
      let mem ← counterInputMem 7 5
      let (regs, finalMem) ← evalWalkArgToStack? rhsStackOffset mem
      pure (regs .br1 == 5 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 5) &&
        regs .br7 == mmInputStart + BitVec.ofNat 64 (counterArg0Offset + 8))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← counterInputMem 7 5
      let (_, walkedMem) ← evalWalkArgToStack? rhsStackOffset mem
      let (_, absMem) ← evalAbsArgToStack? mem
      pure (loadv .m64 walkedMem rhsStackAddr == loadv .m64 absMem rhsStackAddr &&
        loadv .m64 walkedMem rhsStackAddr == some (.vlong 5))) with
  | some true => true
  | _ => false

-- E∞ knife 2: two consecutive walked r7 args (`svm-sem-007`)
#guard
  match (do
      let mem ← counterInputMem2 7 5 9
      let (regs, finalMem) ← evalWalkTwoArgsToStack? mem
      pure (loadv .m64 finalMem rhsStackAddr == some (.vlong 5) &&
        loadv .m64 finalMem lhsStackAddr == some (.vlong 9) &&
        regs .br1 == 9 &&
        regs .br7 == mmInputStart + BitVec.ofNat 64 (counterArg0Offset + 16))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← counterInputMem2 7 5 9
      let (_, walkedMem) ← evalWalkTwoArgsToStack? mem
      let (_, abs0Mem) ← evalAbsArgToStack? mem
      let (_, abs1Mem) ← evalAbsArg1ToStack? mem
      pure (loadv .m64 walkedMem rhsStackAddr == loadv .m64 abs0Mem rhsStackAddr &&
        loadv .m64 walkedMem lhsStackAddr == loadv .m64 abs1Mem lhsStackAddr &&
        loadv .m64 walkedMem rhsStackAddr == some (.vlong 5) &&
        loadv .m64 walkedMem lhsStackAddr == some (.vlong 9))) with
  | some true => true
  | _ => false

-- E∞ knife 3: Loader account-0 header/key walk (`svm-sem-008`)
#guard (walkAccount0Meta? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0MetaInputMem 7 5 0x42
      let (regs, finalMem) ← evalWalkAccount0MetaToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x42 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x42))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0MetaInputMem 7 5 0x42
      let (regs, _) ← evalWalkAccount0MetaToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount0Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == account0NonDupMarker && key == 0x42)) with
  | some true => true
  | _ => false

-- E∞ knife 4: Loader account-0 signer/writable flags (`svm-sem-009`)
#guard (walkAccount0Flags? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0FlagsInputMem 7 5 0x42 1 1
      let (regs, finalMem) ← evalWalkAccount0FlagsToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0FlagsInputMem 7 5 0x42 1 0
      let (regs, _) ← evalWalkAccount0FlagsToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount0Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) with
  | some true => true
  | _ => false


-- E∞ knife 5: Loader account-0 lamports/data_len (`svm-sem-010`)
#guard (walkAccount0Budget? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0BudgetInputMem 7 5 0x42 1000 128
      let (regs, finalMem) ← evalWalkAccount0BudgetToStack? rhsStackOffset mem
      pure (regs .br1 == 1000 && regs .br2 == 128 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1000))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0BudgetInputMem 7 5 0x42 1000 128
      let (regs, _) ← evalWalkAccount0BudgetToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount0Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 1000 && dataLen == 128)) with
  | some true => true
  | _ => false


-- E∞ knife 6: Loader account-0 owner limbs (`svm-sem-011`)
#guard (walkAccount0Owner? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0OwnerInputMem 7 5 0x42 0xA1 0xB2
      let (regs, finalMem) ← evalWalkAccount0OwnerToStack? rhsStackOffset mem
      pure (regs .br1 == 0xA1 && regs .br2 == 0xB2 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xA1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0OwnerInputMem 7 5 0x42 0xA1 0xB2
      let (regs, _) ← evalWalkAccount0OwnerToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount0Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xA1 && owner1 == 0xB2)) with
  | some true => true
  | _ => false

-- E∞ knife 7: Loader account-0 owner limbs 2/3 (`svm-sem-012`)
#guard (walkAccount0OwnerHi? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0OwnerHiInputMem 7 5 0x42 0xC3 0xD4
      let (regs, finalMem) ← evalWalkAccount0OwnerHiToStack? rhsStackOffset mem
      pure (regs .br1 == 0xC3 && regs .br2 == 0xD4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xC3))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0OwnerHiInputMem 7 5 0x42 0xC3 0xD4
      let (regs, _) ← evalWalkAccount0OwnerHiToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount0OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0xC3 && owner3 == 0xD4)) with
  | some true => true
  | _ => false

-- E∞ knife 8: Loader account-0 executable + rent_epoch (`svm-sem-013`)
#guard (walkAccount0ExecRent? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0ExecRentInputMem 7 5 0x42 1 0xEE
      let (regs, finalMem) ← evalWalkAccount0ExecRentToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0ExecRentInputMem 7 5 0x42 0 0xEE
      let (regs, _) ← evalWalkAccount0ExecRentToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount0ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) with
  | some true => true
  | _ => false

-- E∞ knife 9: Loader account-0 → next-account marker skip (`svm-sem-014`)
#guard (walkAccount0SkipNext? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account0SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE
      let (regs, finalMem) ← evalWalkAccount0SkipNextToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account0SkipNextInputMem 7 5 0x42 0xAB 0xEE
      let (regs, _) ← evalWalkAccount0SkipNextToStack? rhsStackOffset mem
      let marker ← evalAbsAccount1Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) with
  | some true => true
  | _ => false


-- E∞ knife 10: Loader account-1 header/key after skip (`svm-sem-015`)
#guard (walkAccount1MetaAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71
      let (regs, finalMem) ← evalWalkAccount1MetaAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x71 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x71))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1MetaInputMem 7 5 0x42 0xAB 0xEE 0x71
      let (regs, _) ← evalWalkAccount1MetaAfterSkipToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount1Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAB && key == 0x71)) with
  | some true => true
  | _ => false


-- E∞ knife 11: Loader account-1 signer/writable flags after skip (`svm-sem-016`)
#guard (walkAccount1FlagsAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1
      let (regs, finalMem) ← evalWalkAccount1FlagsAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1FlagsInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0
      let (regs, _) ← evalWalkAccount1FlagsAfterSkipToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount1Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) with
  | some true => true
  | _ => false


-- E∞ knife 12: Loader account-1 lamports/data_len after skip (`svm-sem-017`)
#guard (walkAccount1BudgetAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
      let (regs, finalMem) ← evalWalkAccount1BudgetAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1000 && regs .br2 == 128 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1000))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1BudgetInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128
      let (regs, _) ← evalWalkAccount1BudgetAfterSkipToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount1Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 1000 && dataLen == 128)) with
  | some true => true
  | _ => false

-- E∞ knife 13: Loader account-1 owner limbs 0/1 after skip (`svm-sem-018`)
#guard (walkAccount1OwnerAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128 0xA1 0xB2
      let (regs, finalMem) ← evalWalkAccount1OwnerAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 0xA1 && regs .br2 == 0xB2 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xA1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1OwnerInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2
      let (regs, _) ← evalWalkAccount1OwnerAfterSkipToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount1Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xA1 && owner1 == 0xB2)) with
  | some true => true
  | _ => false

-- E∞ knife 14: Loader account-1 owner limbs 2/3 after skip (`svm-sem-019`)
#guard (walkAccount1OwnerHiAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4
      let (regs, finalMem) ← evalWalkAccount1OwnerHiAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 0xC3 && regs .br2 == 0xD4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xC3))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1OwnerHiInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2 0xC3 0xD4
      let (regs, _) ← evalWalkAccount1OwnerHiAfterSkipToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount1OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0xC3 && owner3 == 0xD4)) with
  | some true => true
  | _ => false

-- E∞ knife 15: Loader account-1 executable/rent after skip (`svm-sem-020`)
#guard (walkAccount1ExecRentAfterSkip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE
      let (regs, finalMem) ← evalWalkAccount1ExecRentAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1ExecRentInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2 0xC3 0xD4 0 0xEE
      let (regs, _) ← evalWalkAccount1ExecRentAfterSkipToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount1ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) with
  | some true => true
  | _ => false

-- E∞ knife 16: Loader account-1 → account-2 skip chain (`svm-sem-021`)
#guard (walkAccount1SkipNextAfterAccount0Skip? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account1SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount1SkipNextAfterAccount0SkipToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account1SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAB
      let (regs, _) ← evalWalkAccount1SkipNextAfterAccount0SkipToStack? rhsStackOffset mem
      let marker ← evalAbsAccount2Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) with
  | some true => true
  | _ => false

-- E∞ knife 17: Loader account-2 header/key after skip chain (`svm-sem-022`)
#guard (walkAccount2MetaAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72
      let (regs, finalMem) ← evalWalkAccount2MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x72 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x72))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72
      let (regs, _) ← evalWalkAccount2MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount2Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAC && key == 0x72)) with
  | some true => true
  | _ => false

-- E∞ knife 18: Loader account-2 signer/writable after skip chain (`svm-sem-023`)
#guard (walkAccount2FlagsAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1
      let (regs, finalMem) ← evalWalkAccount2FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0
      let (regs, _) ← evalWalkAccount2FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount2Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) with
  | some true => true
  | _ => false

-- E∞ knife 19: Loader account-2 lamports/data_len after skip chain (`svm-sem-024`)
#guard (walkAccount2BudgetAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
      let (regs, finalMem) ← evalWalkAccount2BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 2000 && regs .br2 == 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 2000))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64
      let (regs, _) ← evalWalkAccount2BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount2Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 2000 && dataLen == 64)) with
  | some true => true
  | _ => false

-- E∞ knife 20: Loader account-2 owner limbs 0/1 after skip chain (`svm-sem-025`)
#guard (walkAccount2OwnerAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6
      let (regs, finalMem) ← evalWalkAccount2OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE5 && regs .br2 == 0xF6 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE5))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6
      let (regs, _) ← evalWalkAccount2OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount2Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE5 && owner1 == 0xF6)) with
  | some true => true
  | _ => false

-- E∞ knife 21: Loader account-2 owner limbs 2/3 after skip chain (`svm-sem-026`)
#guard (walkAccount2OwnerHiAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28
      let (regs, finalMem) ← evalWalkAccount2OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x17 && regs .br2 == 0x28 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x17))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28
      let (regs, _) ← evalWalkAccount2OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount2OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x17 && owner3 == 0x28)) with
  | some true => true
  | _ => false

-- E∞ knife 22: Loader account-2 executable/rent after skip chain (`svm-sem-027`)
#guard (walkAccount2ExecRentAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE
      let (regs, finalMem) ← evalWalkAccount2ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE
      let (regs, _) ← evalWalkAccount2ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount2ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) with
  | some true => true
  | _ => false

-- E∞ knife 23: Loader account-2 → account-3 skip chain (`svm-sem-028`)
#guard (walkAccount2SkipNextAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account2SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount2SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account2SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB
      let (regs, _) ← evalWalkAccount2SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount3Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) with
  | some true => true
  | _ => false

-- E∞ knife 24: Loader account-3 header/key after skip chain (`svm-sem-029`)
#guard (walkAccount3MetaAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73
      let (regs, finalMem) ← evalWalkAccount3MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x73 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x73))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73
      let (regs, _) ← evalWalkAccount3MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount3Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAB && key == 0x73)) with
  | some true => true
  | _ => false

-- E∞ knife 25: Loader account-3 signer/writable after skip chain (`svm-sem-030`)
#guard (walkAccount3FlagsAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73 1 1
      let (regs, finalMem) ← evalWalkAccount3FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0
      let (regs, _) ← evalWalkAccount3FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount3Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) with
  | some true => true
  | _ => false

-- E∞ knife 26: Loader account-3 lamports/data_len after skip chain (`svm-sem-031`)
#guard (walkAccount3BudgetAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73 1 1 3000 96
      let (regs, finalMem) ← evalWalkAccount3BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 3000 && regs .br2 == 96 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 3000))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96
      let (regs, _) ← evalWalkAccount3BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount3Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 3000 && dataLen == 96)) with
  | some true => true
  | _ => false

-- E∞ knife 27: Loader account-3 owner limbs 0/1 after skip chain (`svm-sem-032`)
#guard (walkAccount3OwnerAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7
      let (regs, finalMem) ← evalWalkAccount3OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE6 && regs .br2 == 0xF7 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE6))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7
      let (regs, _) ← evalWalkAccount3OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount3Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE6 && owner1 == 0xF7)) with
  | some true => true
  | _ => false

-- E∞ knife 28: Loader account-3 owner limbs 2/3 after skip chain (`svm-sem-033`)
#guard (walkAccount3OwnerHiAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29
      let (regs, finalMem) ← evalWalkAccount3OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x18 && regs .br2 == 0x29 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x18))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29
      let (regs, _) ← evalWalkAccount3OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount3OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x18 && owner3 == 0x29)) with
  | some true => true
  | _ => false

-- E∞ knife 29: Loader account-3 executable/rent after skip chain (`svm-sem-034`)
#guard (walkAccount3ExecRentAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE
      let (regs, finalMem) ← evalWalkAccount3ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE
      let (regs, _) ← evalWalkAccount3ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount3ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) with
  | some true => true
  | _ => false

-- E∞ knife 30: Loader account-3 → account-4 skip chain (`svm-sem-035`)
#guard (walkAccount3SkipNextAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account3SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount3SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account3SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAC
      let (regs, _) ← evalWalkAccount3SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount4Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAC)) with
  | some true => true
  | _ => false

-- E∞ knife 31: Loader account-4 header/key after skip chain (`svm-sem-036`)
#guard (walkAccount4MetaAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74
      let (regs, finalMem) ← evalWalkAccount4MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x74 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x74))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74
      let (regs, _) ← evalWalkAccount4MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount4Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAD && key == 0x74)) with
  | some true => true
  | _ => false

-- E∞ knife 32: Loader account-4 signer/writable after skip chain (`svm-sem-037`)
#guard (walkAccount4FlagsAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1
      let (regs, finalMem) ← evalWalkAccount4FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0
      let (regs, _) ← evalWalkAccount4FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount4Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) with
  | some true => true
  | _ => false

-- E∞ knife 33: Loader account-4 lamports/data_len after skip chain (`svm-sem-038`)
#guard (walkAccount4BudgetAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112
      let (regs, finalMem) ← evalWalkAccount4BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 4000 && regs .br2 == 112 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 4000))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112
      let (regs, _) ← evalWalkAccount4BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount4Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 4000 && dataLen == 112)) with
  | some true => true
  | _ => false

-- E∞ knife 34: Loader account-4 owner limbs 0/1 after skip chain (`svm-sem-039`)
#guard (walkAccount4OwnerAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8
      let (regs, finalMem) ← evalWalkAccount4OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE7 && regs .br2 == 0xF8 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE7))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8
      let (regs, _) ← evalWalkAccount4OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount4Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE7 && owner1 == 0xF8)) with
  | some true => true
  | _ => false

-- E∞ knife 35: Loader account-4 owner limbs 2/3 after skip chain (`svm-sem-040`)
#guard (walkAccount4OwnerHiAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A
      let (regs, finalMem) ← evalWalkAccount4OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x19 && regs .br2 == 0x2A &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x19))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A
      let (regs, _) ← evalWalkAccount4OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount4OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x19 && owner3 == 0x2A)) with
  | some true => true
  | _ => false

-- E∞ knife 36: Loader account-4 executable/rent after skip chain (`svm-sem-041`)
#guard (walkAccount4ExecRentAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF
      let (regs, finalMem) ← evalWalkAccount4ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEF &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF
      let (regs, _) ← evalWalkAccount4ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount4ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEF)) with
  | some true => true
  | _ => false

-- E∞ knife 37: Loader account-4 → account-5 skip chain (`svm-sem-042`)
#guard (walkAccount4SkipNextAfterSkipChain? rhsStackOffset).isSome
#guard
  match (do
      let mem ← account4SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount4SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) with
  | some true => true
  | _ => false
#guard
  match (do
      let mem ← account4SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAE
      let (regs, _) ← evalWalkAccount4SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount5Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAE)) with
  | some true => true
  | _ => false

end Tests.SolanalibSpec

