import ProofForge.Svm.IR
import ProofForge.Svm.ABI
import Solanalib.SBPF.Interpreter
import Solanalib.SBPF.Verifier

namespace ProofForge.Svm.Solanalib

open _root_.Solanalib.SBPF

/-- The current textual emitter uses classic `alu64 mul/div/mod`, which Solanalib models as v1. -/
def version : SBPFV := .v1

def memoryChunk? : Nat → Option MemoryChunk
  | 1 => some .m8
  | 2 => some .m16
  | 4 => some .m32
  | 8 => some .m64
  | _ => none

/-- sBPF memory offsets are signed 16-bit values. This experiment accepts positive offsets only. -/
private def positiveOffset? (offset : Nat) : Option U16 :=
  if offset < 2 ^ 15 then some (BitVec.ofNat 16 offset) else none

/--
The typed counterpart of the emitter's `stx* [r6 + ACC0_DATA + slot.offset], valueReg`.
It covers static account-data writes only; Loader input construction remains outside Solanalib.
-/
def staticStoreInstruction? (slot : IR.Slot) (valueReg : BpfIReg := .br1) :
    Option BpfInstruction := do
  let chunk ← memoryChunk? slot.width
  let offset ← positiveOffset? (ABI.acc0Data + slot.offset)
  return .st chunk .br6 (.reg valueReg) offset

/-- Resolve a Core place through the SVM target layout before constructing a typed instruction. -/
def staticStoreAt? (program : IR.Program) (place : Core.Place)
    (valueReg : BpfIReg := .br1) : Option BpfInstruction := do
  let slot ← program.slots.find? (·.place == some place)
  staticStoreInstruction? slot valueReg

def arithBinop : Core.CheckedArith → Binop
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod

/-- The source-level success condition emitted before each classic v1 arithmetic operation. -/
def checkedArithGuard : Core.CheckedArith → U64 → U64 → Bool
  | .add, lhs, rhs => lhs.ule (u64Max - rhs)
  | .sub, lhs, rhs => rhs.ule lhs
  | .mul, lhs, rhs => rhs == 0 || lhs.ule (u64Max / rhs)
  | .div, _, rhs => rhs != 0
  | .mod, _, rhs => rhs != 0

/-- The two typed ALU instructions corresponding to `mov64 r4, r1; op64 r4, r2`. -/
def checkedArithBody (kind : Core.CheckedArith) : EbpfAsm :=
  [.alu64 .mov .br4 (.reg .br1), .alu64 (arithBinop kind) .br4 (.reg .br2)]

structure CheckedWriteFragment where
  compute : EbpfAsm
  store : BpfInstruction
  deriving Repr, DecidableEq

/--
Bounded Core-to-ISA bridge: one checked calculation followed by one statically addressed write.
The checked guard and operand loads remain outside this fragment.
-/
def checkedWriteFragment? {ValExt : Type} (program : IR.Program) (write : Core.StateWrite ValExt) :
    Option CheckedWriteFragment := do
  let kind ← match write.value with | .checked kind _ _ => some kind | _ => none
  let store ← staticStoreAt? program write.place .br4
  return { compute := checkedArithBody kind, store }

/-- A checked-add CFG terminator together with the typed local instruction sequence that selects
its success/overflow edge. Labels are normalized to one contiguous fragment: the conditional jump
skips the six success instructions and lands at the local overflow endpoint. -/
structure CheckedAddCFGWriteFragment where
  success : Core.CFG.BlockId
  overflow : Core.CFG.BlockId
  guard : EbpfAsm
  successBody : EbpfAsm
  deriving Repr, DecidableEq

private def checkedResultOffset : U16 := 0xffe8

/-- `lddw r3, u64Max; sub64 r3, r2; jgt r1, r3, overflow`. The offset skips the
success body below, including the normalized block-edge `ja`. -/
def checkedAddGuardBody : EbpfAsm :=
  [ .ldImm .br3 0xffffffff 0xffffffff,
    .alu64 .sub .br3 (.reg .br2),
    .jump .gt .br1 (.reg .br3) 6 ]

theorem checkedAddOverflow_eq_not_guard (lhs rhs : U64) :
    (u64Max - rhs).ult lhs = !checkedArithGuard .add lhs rhs := by
  simp [checkedArithGuard]
  bv_decide

/-- The checked-add success edge exactly retains the emitter's `r10-24` result handoff before the
statically resolved account-data store. The `ja 0` is the local normalization of the CFG edge. -/
def checkedAddSuccessBody (store : BpfInstruction) : EbpfAsm :=
  checkedArithBody .add ++
    [ .st .m64 .br10 (.reg .br4) checkedResultOffset,
      .ja 0,
      .ldx .m64 .br1 .br10 checkedResultOffset,
      store ]

def checkedAddControlFragment (success overflow : Core.CFG.BlockId)
    (store : BpfInstruction) : CheckedAddCFGWriteFragment := {
  success
  overflow
  guard := checkedAddGuardBody
  successBody := checkedAddSuccessBody store
}

/--
Resolve one real SVM CFG checked-add edge and one Core static write to a typed Solanalib fragment.
The bridge is deliberately fail-closed: it requires zero-argument edges, a field lhs matching the
resolved physical slot, and a Core evaluation write for the same checked operation.
-/
def checkedAddCFGWriteFragment? (program : IR.Program) (graph : IR.CFG)
    (blockId : Core.CFG.BlockId) (write : Core.StateWrite Ops.ValKind) :
    Option CheckedAddCFGWriteFragment := do
  let block ← graph.block? blockId
  let (lhs, rhs, fieldName, success, overflow) ← match block.terminator with
    | .checked (.addU64 lhs@(.field _ fieldName) rhs) success overflow =>
        some (lhs, rhs, fieldName, success, overflow)
    | _ => none
  if !success.args.isEmpty || !overflow.args.isEmpty then none else
  let (kind, writeLhs, writeRhs) ← match write.value with
    | .checked kind lhs rhs => some (kind, lhs, rhs)
    | _ => none
  if kind != .add || lhs != writeLhs || rhs != writeRhs then none else
  let slot ← program.slots.find? (·.place == some write.place)
  if slot.name != fieldName then none else
  let store ← staticStoreInstruction? slot .br1
  return checkedAddControlFragment success.target overflow.target store

/-- All instructions in the bounded arithmetic bridge satisfy Solanalib's v1 verifier. -/
theorem checkedArithBody_verified (kind : Core.CheckedArith) :
    (checkedArithBody kind).all (verifyInstr · version) = true := by
  cases kind <;> decide

/-- The checked-add branch, scratch handoff, edge jump, reload, and static store all satisfy the
instruction-level part of Solanalib's v1 verifier. -/
theorem checkedAddControl_verified (store : BpfInstruction)
    (hstore : verifyInstr store version = true) :
    (checkedAddGuardBody ++ checkedAddSuccessBody store).all
      (verifyInstr · version) = true := by
  simpa [checkedAddGuardBody, checkedAddSuccessBody, checkedArithBody, arithBinop,
    version, verifyInstr, verifyAlu, checkImmNonzero] using hstore

def arithInputRegs (lhs rhs : U64) : RegMap :=
  setReg (setReg initRegMap .br1 lhs) .br2 rhs

private def evalAluBody : List BpfInstruction → RegMap → RegOutcome
  | [], regs => .oks regs
  | .alu64 op dst src :: rest, regs =>
      match evalAlu64 op dst src regs true with
      | .oks next => evalAluBody rest next
      | other => other
  | _ :: _, _ => .nok

/-- Execute only the typed arithmetic fragment above, using Solanalib's operation semantics. -/
def evalCheckedArithBody (kind : Core.CheckedArith) (lhs rhs : U64) : RegOutcome :=
  evalAluBody (checkedArithBody kind) (arithInputRegs lhs rhs)

/-- The typed add fragment computes the same 64-bit result as Solanalib's word addition. -/
theorem evalCheckedAdd (lhs rhs : U64) :
    evalCheckedArithBody .add lhs rhs =
      .oks (setReg (arithInputRegs lhs rhs) .br4 (lhs + rhs)) := by
  simp [evalCheckedArithBody, evalAluBody, checkedArithBody, arithBinop,
    evalAlu64, sndOp64, arithInputRegs, setReg]
  funext reg
  by_cases h : reg = .br4 <;> simp [setReg, h]

/--
Execute the bounded source guard, typed ALU body, and typed static store as one fragment.
`r6` is the Loader input base and the result in `r4` is the store source.
-/
def evalCheckedWrite? (slot : IR.Slot) (kind : Core.CheckedArith) (lhs rhs : U64)
    (memory : Mem) : Option Mem := do
  if !checkedArithGuard kind lhs rhs then none
  let input := setReg (arithInputRegs lhs rhs) .br6 mmInputStart
  let regs ←
    match evalAluBody (checkedArithBody kind) input with
    | .oks regs => some regs
    | .nok | .okn => none
  let instruction ← staticStoreInstruction? slot .br4
  match instruction with
  | .st chunk dst src offset => evalStore chunk dst src offset regs memory
  | _ => none

/--
End-to-end bounded simulation for Counter's real value slot: when the source add guard
succeeds, Solanalib's typed ALU+store semantics writes exactly the checked sum.
-/
theorem checkedAddWrite_simulates (lhs rhs : U64)
    (hguard : checkedArithGuard .add lhs rhs = true) :
    evalCheckedWrite?
      { name := "value", offset := 8, width := 8, abi := "u64-le" }
      .add lhs rhs initMem =
    storev .m64 initMem (mmInputStart + 104) (.vlong (lhs + rhs)) := by
  simp [evalCheckedWrite?, hguard, checkedArithBody, arithBinop, evalAluBody,
    evalAlu64, sndOp64, arithInputRegs, staticStoreInstruction?, memoryChunk?,
    positiveOffset?, evalStore, memoryChunkValueOfU64, setReg, ABI.acc0Data]

/-- Execute one typed static-store instruction through Solanalib's memory semantics. -/
def evalStaticStore? (slot : IR.Slot) (regs : RegMap) (memory : Mem) : Option Mem := do
  let instruction ← staticStoreInstruction? slot
  match instruction with
  | .st chunk dst src offset => evalStore chunk dst src offset regs memory
  | _ => none

private def stepDecoded (instruction : BpfInstruction) : BpfState → BpfState
  | .ok pc regs memory stack sv functions current remaining =>
      step pc instruction regs memory stack sv functions false 0 current remaining
  | state => state

private def runDecoded : EbpfAsm → BpfState → BpfState
  | [], state => state
  | instruction :: rest, state => runDecoded rest (stepDecoded instruction state)

/-- Execute the emitted checked-add guard and project its selected local edge. `true` is the
fallthrough success edge; `false` is the taken overflow edge. -/
def evalCheckedAddGuard (lhs rhs : U64) (memory : Mem) : Option (Bool × Mem) :=
  let input := setReg (setReg initRegMap .br1 lhs) .br2 rhs
  let loaded := evalLoadImm .br3 0xffffffff 0xffffffff input
  match evalAlu64 .sub .br3 (.reg .br2) loaded true with
  | .oks regs => some (!evalJmp .gt .br1 (.reg .br3) regs, memory)
  | .okn | .nok => none

/-- Solanalib's decoded `jgt` selects exactly the source checked-add guard and does not mutate
memory on either edge. -/
theorem evalCheckedAddGuard_corresponds (lhs rhs : U64) (memory : Mem) :
    evalCheckedAddGuard lhs rhs memory =
      some (checkedArithGuard .add lhs rhs, memory) := by
  simp [evalCheckedAddGuard, evalLoadImm, evalAlu64, sndOp64, evalJmp, setReg,
    checkedArithGuard, u64Max]
  bv_decide

/-- On the source success condition, the typed branch selects success and the existing typed
ALU/static-store simulation writes the exact sum to Counter's physical value slot. -/
theorem checkedAddControl_success_simulates (lhs rhs : U64)
    (hguard : checkedArithGuard .add lhs rhs = true) :
    evalCheckedAddGuard lhs rhs initMem = some (true, initMem) ∧
      evalCheckedWrite?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
        .add lhs rhs initMem =
      storev .m64 initMem (mmInputStart + 104) (.vlong (lhs + rhs)) := by
  constructor
  · rw [evalCheckedAddGuard_corresponds, hguard]
  · exact checkedAddWrite_simulates lhs rhs hguard

/-- On overflow, the decoded conditional jump selects the overflow edge with memory unchanged. -/
theorem checkedAddControl_overflow_preserves (lhs rhs : U64) (memory : Mem)
    (hguard : checkedArithGuard .add lhs rhs = false) :
    evalCheckedAddGuard lhs rhs memory = some (false, memory) := by
  rw [evalCheckedAddGuard_corresponds, hguard]

inductive CheckedCFGWriteOutcome where
  | success (target : Core.CFG.BlockId) (memory : Mem)
  | overflow (target : Core.CFG.BlockId) (memory : Mem)

/-- Execute the decoded checked-add control fragment through Solanalib's small-step semantics.
PC 4 is the guard fallthrough; PC 10 is both the end of the success body and the overflow target. -/
def evalCheckedAddCFGWrite (fragment : CheckedAddCFGWriteFragment) (lhs rhs : U64)
    (memory : Mem) : Option CheckedCFGWriteOutcome :=
  let regs := setReg (setReg (setReg initRegMap .br1 lhs) .br2 rhs) .br6 mmInputStart
  let guarded := runDecoded fragment.guard (initBpfState regs memory 32 version)
  match guarded with
  | .ok pc _ guardedMemory _ _ _ _ _ =>
      if pc == 4 then
        match runDecoded fragment.successBody guarded with
        | .ok finalPc _ finalMemory _ _ _ _ _ =>
            if finalPc == 10 then some (.success fragment.success finalMemory) else none
        | .success _ | .eflag | .err => none
      else if pc == 10 then
        some (.overflow fragment.overflow guardedMemory)
      else none
  | .success _ | .eflag | .err => none

end ProofForge.Svm.Solanalib
