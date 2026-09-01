import ProofForge.Svm.IR
import ProofForge.Svm.ABI
import ProofForge.Svm.Sdk.StorageModel
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
  | .mul, lhs, rhs => if rhs = 0 then true else lhs.ule (u64Max / rhs)
  | .div, _, rhs => rhs != 0
  | .mod, _, rhs => rhs != 0

private theorem beqZero_eq_not_bneZero (value : U64) :
    (value == 0) = !(value != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq]

/-- The two typed ALU instructions corresponding to `mov64 r4, r1; op64 r4, r2`. -/
def checkedArithBody (kind : Core.CheckedArith) : EbpfAsm :=
  [.alu64 .mov .br4 (.reg .br1), .alu64 (arithBinop kind) .br4 (.reg .br2)]

def checkedArithResult : Core.CheckedArith → U64 → U64 → U64
  | .add, lhs, rhs => lhs + rhs
  | .sub, lhs, rhs => lhs - rhs
  | .mul, lhs, rhs => lhs * rhs
  | .div, lhs, rhs => lhs / rhs
  | .mod, lhs, rhs => lhs % rhs

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

/-- A checked-arithmetic CFG terminator together with the typed local instruction sequence that
selects its success/overflow edge. Labels are normalized to one contiguous fragment. -/
structure CheckedCFGWriteFragment where
  kind : Core.CheckedArith
  success : Core.CFG.BlockId
  overflow : Core.CFG.BlockId
  guard : EbpfAsm
  successBody : EbpfAsm
  deriving Repr, BEq

private def checkedResultOffset : U16 := 0xffe8

/-- Exact decoded guard shape emitted for each checked arithmetic operation. Every overflow jump
skips the six-instruction success body. The multiply zero case skips its quotient guard. -/
def checkedGuardBody : Core.CheckedArith → EbpfAsm
  | .add =>
      [ .ldImm .br3 0xffffffff 0xffffffff,
        .alu64 .sub .br3 (.reg .br2),
        .jump .gt .br1 (.reg .br3) 6 ]
  | .sub => [.jump .lt .br1 (.reg .br2) 6]
  | .mul =>
      [ .ldImm .br3 0xffffffff 0xffffffff,
        .jump .eq .br2 (.imm 0) 2,
        .alu64 .div .br3 (.reg .br2),
        .jump .gt .br1 (.reg .br3) 6 ]
  | .div | .mod => [.jump .eq .br2 (.imm 0) 6]

/-- Local PC at which a successful guard falls through into its arithmetic body. -/
def checkedSuccessPC : Core.CheckedArith → U64
  | .add => 4
  | .sub | .div | .mod => 1
  | .mul => 5

/-- Local PC shared by the overflow edge and the end of the six-instruction success body. -/
def checkedEndPC (kind : Core.CheckedArith) : U64 := checkedSuccessPC kind + 6

/-- Every success edge retains the emitter's `r10-24` result handoff before the statically
resolved account-data store. The `ja 0` is the local normalization of the CFG edge. -/
def checkedSuccessBody (kind : Core.CheckedArith) (store : BpfInstruction) : EbpfAsm :=
  checkedArithBody kind ++
    [ .st .m64 .br10 (.reg .br4) checkedResultOffset,
      .ja 0,
      .ldx .m64 .br1 .br10 checkedResultOffset,
      store ]

def checkedControlFragment (kind : Core.CheckedArith) (success overflow : Core.CFG.BlockId)
    (store : BpfInstruction) : CheckedCFGWriteFragment := {
  kind
  success
  overflow
  guard := checkedGuardBody kind
  successBody := checkedSuccessBody kind store
}

/--
Resolve one real SVM CFG checked-arithmetic edge and one Core static write to a typed fragment.
The bridge is deliberately fail-closed: it requires zero-argument edges, a field lhs matching the
resolved physical slot, and a Core evaluation write for the same checked operation.
-/
def checkedCFGWriteFragment? (program : IR.Program) (graph : IR.CFG)
    (blockId : Core.CFG.BlockId) (write : Core.StateWrite Ops.ValKind) :
    Option CheckedCFGWriteFragment := do
  let block ← graph.block? blockId
  let (kind, lhs, rhs, fieldName, success, overflow) ← match block.terminator with
    | .checked operation success overflow =>
        match operation with
        | .addU64 lhs@(.field _ fieldName) rhs =>
            some (.add, lhs, rhs, fieldName, success, overflow)
        | .subU64 lhs@(.field _ fieldName) rhs =>
            some (.sub, lhs, rhs, fieldName, success, overflow)
        | .mulU64 lhs@(.field _ fieldName) rhs =>
            some (.mul, lhs, rhs, fieldName, success, overflow)
        | .divU64 lhs@(.field _ fieldName) rhs =>
            some (.div, lhs, rhs, fieldName, success, overflow)
        | .modU64 lhs@(.field _ fieldName) rhs =>
            some (.mod, lhs, rhs, fieldName, success, overflow)
        | _ => none
    | _ => none
  if !success.args.isEmpty || !overflow.args.isEmpty then none else
  let (writeKind, writeLhs, writeRhs) ← match write.value with
    | .checked writeKind lhs rhs => some (writeKind, lhs, rhs)
    | _ => none
  if kind != writeKind || lhs != writeLhs || rhs != writeRhs then none else
  let slot ← program.slots.find? (·.place == some write.place)
  if slot.name != fieldName then none else
  let store ← staticStoreInstruction? slot .br1
  return checkedControlFragment kind success.target overflow.target store

/-- All instructions in the bounded arithmetic bridge satisfy Solanalib's v1 verifier. -/
theorem checkedArithBody_verified (kind : Core.CheckedArith) :
    (checkedArithBody kind).all (verifyInstr · version) = true := by
  cases kind <;> decide

/-- Every checked branch, scratch handoff, edge jump, reload, and static store satisfies the
instruction-level part of Solanalib's v1 verifier. -/
theorem checkedControl_verified (kind : Core.CheckedArith) (store : BpfInstruction)
    (hstore : verifyInstr store version = true) :
    (checkedGuardBody kind ++ checkedSuccessBody kind store).all
      (verifyInstr · version) = true := by
  cases kind <;>
    simpa [checkedGuardBody, checkedSuccessBody, checkedArithBody, arithBinop,
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

/-- On every source-valid checked edge, the emitted ALU body computes the corresponding 64-bit
operation in `r4`. Division and modulo validity discharge Solanalib's zero-divisor flag. -/
theorem evalCheckedArithBody_corresponds (kind : Core.CheckedArith) (lhs rhs : U64)
    (hguard : checkedArithGuard kind lhs rhs = true) :
    evalCheckedArithBody kind lhs rhs =
      .oks (setReg (arithInputRegs lhs rhs) .br4 (checkedArithResult kind lhs rhs)) := by
  cases kind with
  | add | sub | mul =>
      simp [evalCheckedArithBody, evalAluBody, checkedArithBody, arithBinop,
        checkedArithResult, evalAlu64, sndOp64, arithInputRegs, setReg]
      funext reg
      by_cases h : reg = .br4 <;> simp [setReg, h]
  | div | mod =>
      have hne : rhs ≠ 0 := by
        intro hzero
        subst rhs
        simp [checkedArithGuard] at hguard
      simp [evalCheckedArithBody, evalAluBody, checkedArithBody, arithBinop,
        checkedArithResult, evalAlu64, sndOp64, arithInputRegs, setReg]
      split <;> simp_all
      subst_vars
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

private def decodedSlots : BpfInstruction → Nat
  | .ldImm .. => 2
  | _ => 1

private def decodedInstructionAt? : EbpfAsm → Nat → Option BpfInstruction
  | [], _ => none
  | instruction :: rest, pc =>
      if pc == 0 then some instruction
      else if pc < decodedSlots instruction then none
      else decodedInstructionAt? rest (pc - decodedSlots instruction)

/-- Dispatch decoded instructions by the PC produced by upstream `step`. This is needed for the
multiply guard's internal jump over its quotient check; reaching a PC outside the fragment returns
the boundary state to the caller. -/
private def runDecodedFrom (basePC : Nat) (program : EbpfAsm) : BpfState → BpfState :=
  go (program.length + 1)
where
  go : Nat → BpfState → BpfState
    | 0, state => state
    | fuel + 1, state@(.ok pc _ _ _ _ _ _ _) =>
        if pc.toNat < basePC then state
        else match decodedInstructionAt? program (pc.toNat - basePC) with
          | none => state
          | some instruction => go fuel (stepDecoded instruction state)
    | _, state => state

/-- Execute the exact guard operations emitted for one checked arithmetic kind and project the
selected local edge. `true` is fallthrough success; `false` is the taken overflow edge. -/
def evalCheckedGuard (kind : Core.CheckedArith) (lhs rhs : U64)
    (memory : Mem) : Option (Bool × Mem) :=
  let input := setReg (setReg initRegMap .br1 lhs) .br2 rhs
  match kind with
  | .add =>
      let loaded := evalLoadImm .br3 0xffffffff 0xffffffff input
      match evalAlu64 .sub .br3 (.reg .br2) loaded true with
      | .oks regs => some (!evalJmp .gt .br1 (.reg .br3) regs, memory)
      | .okn | .nok => none
  | .sub => some (!evalJmp .lt .br1 (.reg .br2) input, memory)
  | .mul =>
      let loaded := evalLoadImm .br3 0xffffffff 0xffffffff input
      if evalJmp .eq .br2 (.imm 0) loaded then some (true, memory)
      else
        match evalAlu64 .div .br3 (.reg .br2) loaded true with
        | .oks regs => some (!evalJmp .gt .br1 (.reg .br3) regs, memory)
        | .okn | .nok => none
  | .div | .mod => some (!evalJmp .eq .br2 (.imm 0) input, memory)

/-- Solanalib's decoded guard operations select exactly the source checked-arithmetic condition
and do not mutate memory on either edge. -/
theorem evalCheckedGuard_corresponds (kind : Core.CheckedArith) (lhs rhs : U64)
    (memory : Mem) :
    evalCheckedGuard kind lhs rhs memory =
      some (checkedArithGuard kind lhs rhs, memory) := by
  cases kind with
  | add =>
      simp [evalCheckedGuard, evalLoadImm, evalAlu64, sndOp64, evalJmp, setReg,
        checkedArithGuard, u64Max]
      bv_decide
  | sub =>
      simp [evalCheckedGuard, evalJmp, sndOp64, setReg, checkedArithGuard]
      bv_decide
  | mul =>
      by_cases hzero : rhs = (0 : U64)
      · subst rhs
        simp [evalCheckedGuard, evalLoadImm, evalJmp, sndOp64, setReg,
          checkedArithGuard]
      · simp [evalCheckedGuard, evalLoadImm, evalAlu64, evalJmp, sndOp64, setReg,
          checkedArithGuard, u64Max]
        split <;> simp_all [setReg] <;> bv_decide
  | div | mod =>
      simpa [evalCheckedGuard, evalJmp, sndOp64, setReg, checkedArithGuard] using
        beqZero_eq_not_bneZero rhs

/-- On a source success condition, every typed guard selects its success edge. -/
theorem checkedControl_selects_success (kind : Core.CheckedArith) (lhs rhs : U64)
    (memory : Mem) (hguard : checkedArithGuard kind lhs rhs = true) :
    evalCheckedGuard kind lhs rhs memory = some (true, memory) := by
  rw [evalCheckedGuard_corresponds, hguard]

/-- On failure, every decoded guard selects the overflow edge with memory unchanged. -/
theorem checkedControl_overflow_preserves (kind : Core.CheckedArith) (lhs rhs : U64)
    (memory : Mem) (hguard : checkedArithGuard kind lhs rhs = false) :
    evalCheckedGuard kind lhs rhs memory = some (false, memory) := by
  rw [evalCheckedGuard_corresponds, hguard]

inductive CheckedCFGWriteOutcome where
  | success (target : Core.CFG.BlockId) (memory : Mem)
  | overflow (target : Core.CFG.BlockId) (memory : Mem)

/-- Execute a decoded checked-arithmetic control fragment through Solanalib's small-step semantics.
The operation-specific guard fallthrough is followed by the same six-instruction success body;
its end PC is also the normalized overflow target. -/
def evalCheckedCFGWrite (fragment : CheckedCFGWriteFragment) (lhs rhs : U64)
    (memory : Mem) : Option CheckedCFGWriteOutcome :=
  let regs := setReg (setReg (setReg initRegMap .br1 lhs) .br2 rhs) .br6 mmInputStart
  let guarded := runDecodedFrom 0 fragment.guard (initBpfState regs memory 32 version)
  match guarded with
  | .ok pc _ guardedMemory _ _ _ _ _ =>
      if pc == checkedSuccessPC fragment.kind then
        match runDecodedFrom (checkedSuccessPC fragment.kind).toNat fragment.successBody guarded with
        | .ok finalPc _ finalMemory _ _ _ _ _ =>
            if finalPc == checkedEndPC fragment.kind then
              some (.success fragment.success finalMemory)
            else none
        | .success _ | .eflag | .err => none
      else if pc == checkedEndPC fragment.kind then
        some (.overflow fragment.overflow guardedMemory)
      else none
  | .success _ | .eflag | .err => none

def cmpCondition : Core.Ops.Cmp → Condition
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

/-- Source-level unsigned comparison selected by a Core CFG branch. -/
def cmpHolds : Core.Ops.Cmp → U64 → U64 → Bool
  | .eq, lhs, rhs => lhs == rhs
  | .ne, lhs, rhs => lhs != rhs
  | .lt, lhs, rhs => lhs.ult rhs
  | .le, lhs, rhs => lhs.ule rhs
  | .gt, lhs, rhs => rhs.ult lhs
  | .ge, lhs, rhs => rhs.ule lhs

/-- The normalized form of `j<cmp> r1, r2, then; ja else`. Local PC 3 denotes the
then edge and PC 2 the else edge, keeping the two external labels distinguishable. -/
def branchBody (cmp : Core.Ops.Cmp) : EbpfAsm :=
  [ .jump (cmpCondition cmp) .br1 (.reg .br2) 2,
    .ja 0 ]

structure CFGBranchFragment where
  cmp : Core.Ops.Cmp
  lhs : Ops.Val
  rhs : Ops.Val
  thenTarget : Core.CFG.BlockId
  elseTarget : Core.CFG.BlockId
  body : EbpfAsm
  deriving Repr, BEq

/-- Resolve one real target-owned SVM CFG branch to its decoded conditional/unconditional jump
pair. Argumented edges remain fail closed until block arguments are lowered by a backend. -/
def cfgBranchFragment? (graph : IR.CFG) (blockId : Core.CFG.BlockId) :
    Option CFGBranchFragment := do
  let block ← graph.block? blockId
  let (cmp, lhs, rhs, thenEdge, elseEdge) ← match block.terminator with
    | .branch cmp lhs rhs thenEdge elseEdge => some (cmp, lhs, rhs, thenEdge, elseEdge)
    | _ => none
  if !thenEdge.args.isEmpty || !elseEdge.args.isEmpty then none else
  return {
    cmp
    lhs
    rhs
    thenTarget := thenEdge.target
    elseTarget := elseEdge.target
    body := branchBody cmp
  }

theorem branchBody_verified (cmp : Core.Ops.Cmp) :
    (branchBody cmp).all (verifyInstr · version) = true := by
  cases cmp <;> decide

/-- Solanalib's decoded unsigned jump condition is exactly the Core comparison relation. -/
theorem evalJmp_corresponds (cmp : Core.Ops.Cmp) (lhs rhs : U64) :
    evalJmp (cmpCondition cmp) .br1 (.reg .br2) (arithInputRegs lhs rhs) =
      cmpHolds cmp lhs rhs := by
  cases cmp <;> simp [cmpCondition, cmpHolds, evalJmp, sndOp64, arithInputRegs, setReg]

private theorem evalJmp_setFramePointer (condition : Condition) (lhs rhs framePointer : U64) :
    evalJmp condition .br1 (.reg .br2)
        (setReg (arithInputRegs lhs rhs) .br10 framePointer) =
      evalJmp condition .br1 (.reg .br2) (arithInputRegs lhs rhs) := by
  cases condition <;> simp [evalJmp, sndOp64, arithInputRegs, setReg]

inductive CFGBranchOutcome where
  | thenEdge (target : Core.CFG.BlockId) (memory : Mem)
  | elseEdge (target : Core.CFG.BlockId) (memory : Mem)

/-- Execute the exact decoded CFG branch pair through upstream small-step semantics. -/
def evalCFGBranch (fragment : CFGBranchFragment) (lhs rhs : U64)
    (memory : Mem) : Option CFGBranchOutcome :=
  let state := runDecodedFrom 0 fragment.body
    (initBpfState (arithInputRegs lhs rhs) memory 8 version)
  match state with
  | .ok pc _ finalMemory _ _ _ _ _ =>
      if pc == 3 then some (.thenEdge fragment.thenTarget finalMemory)
      else if pc == 2 then some (.elseEdge fragment.elseTarget finalMemory)
      else none
  | .success _ | .eflag | .err => none

/-- The exact decoded branch pair selects the same edge as Core and leaves memory unchanged. -/
theorem evalCFGBranch_corresponds (cmp : Core.Ops.Cmp) (lhs rhs : U64)
    (thenTarget elseTarget : Core.CFG.BlockId) (memory : Mem) :
    evalCFGBranch
        { cmp, lhs := .lit 0, rhs := .lit 0, thenTarget, elseTarget,
          body := branchBody cmp }
        lhs rhs memory =
      if cmpHolds cmp lhs rhs then some (.thenEdge thenTarget memory)
      else some (.elseEdge elseTarget memory) := by
  rw [← evalJmp_corresponds cmp lhs rhs]
  by_cases hbranch :
      evalJmp (cmpCondition cmp) .br1 (.reg .br2) (arithInputRegs lhs rhs) = true
  · simp [evalCFGBranch, runDecodedFrom, runDecodedFrom.go, decodedInstructionAt?,
      decodedSlots, branchBody, stepDecoded, step, initBpfState, evalJmp_setFramePointer, hbranch]
  · simp [evalCFGBranch, runDecodedFrom, runDecodedFrom.go, decodedInstructionAt?,
      decodedSlots, branchBody, stepDecoded, step, initBpfState, evalJmp_setFramePointer,
      hbranch]

/-! ## E1 — operand materialization + straightline (`svm-sem-001`)

Counter-shaped emit prefix matching `Emit.checkedCFGTemplate`:

`load field|arg|lit → [r10-8]/[r10-16] → ldxdw r1/r2 → guard → success body/store`.

Covered: field+arg, field+lit, and the composed straightline under Solanalib `step`.
Still out of scope at E1: walked `r7` args, whole-function CFG (E3). AccountWords bridge is E4.
-/

/-- Emitter stack offsets relative to `r10` (negative displacements as unsigned 16-bit). -/
def stackOffset (bytes : Nat) : U16 :=
  BitVec.ofNat 16 ((2 ^ 16 - bytes) % (2 ^ 16))

def lhsStackOffset : U16 := stackOffset 8
def rhsStackOffset : U16 := stackOffset 16

/-- Counter account payload: 8-byte discriminator + 8-byte `value`. -/
def counterAccountDataLen : Nat := 16

/-- Absolute input-region offset of Counter `value` (`ACC0_DATA + 8`). -/
def counterValueOffset : Nat := ABI.acc0Data + 8

/-- Absolute input-region offset of Counter `increment` arg0 (`INSTRUCTION_DATA + 8`). -/
def counterArg0Offset : Nat :=
  (ABI.inputLayoutOf counterAccountDataLen false 1).instructionData + 8

/-- Operand sources materialized by the Counter emit prefix. -/
inductive OperandSource where
  | field (accountOffset : Nat)
  | arg (instructionOffset : Nat)
  | lit (value : U64)
  deriving Repr, DecidableEq

/-- Split a 64-bit immediate into the two halves consumed by `ldImm`. -/
def immHalves (value : U64) : U32 × U32 :=
  (BitVec.ofNat 32 (value.toNat % (2 ^ 32)),
    BitVec.ofNat 32 ((value.toNat / (2 ^ 32)) % (2 ^ 32)))

/-- Typed counterpart of `loadVal` for one Counter-shaped operand into `[r10 + stackOff]`. -/
def materializeOperand? (source : OperandSource) (stackOff : U16) : Option EbpfAsm :=
  match source with
  | .field accountOffset => do
      let off ← positiveOffset? accountOffset
      return [
        .ldx .m64 .br1 .br6 off,
        .st .m64 .br10 (.reg .br1) stackOff]
  | .arg instructionOffset => do
      let off ← positiveOffset? instructionOffset
      return [
        .ldx .m64 .br1 .br6 off,
        .st .m64 .br10 (.reg .br1) stackOff]
  | .lit value =>
      let (lo, hi) := immHalves value
      some [
        .ldImm .br1 lo hi,
        .st .m64 .br10 (.reg .br1) stackOff]

/-- Reload staged operands into `r1`/`r2` exactly as the emitter does. -/
def reloadOperands : EbpfAsm :=
  [ .ldx .m64 .br1 .br10 lhsStackOffset,
    .ldx .m64 .br2 .br10 rhsStackOffset ]

/-- Materialize both operands, reload into `r1`/`r2`, then reuse the E0 control fragment. -/
def checkedStraightlineFragment? (kind : Core.CheckedArith)
    (success overflow : Core.CFG.BlockId) (store : BpfInstruction)
    (lhs rhs : OperandSource) : Option EbpfAsm := do
  let left ← materializeOperand? lhs lhsStackOffset
  let right ← materializeOperand? rhs rhsStackOffset
  let control := checkedControlFragment kind success overflow store
  return left ++ right ++ reloadOperands ++ control.guard ++ control.successBody

/-- Seed Loader input memory with Counter `value` and arg0 words. -/
def counterInputMem (value arg0 : U64) : Option Mem := do
  let m₁ ← storev .m64 initMem (mmInputStart + BitVec.ofNat 64 counterValueOffset) (.vlong value)
  storev .m64 m₁ (mmInputStart + BitVec.ofNat 64 counterArg0Offset) (.vlong arg0)

/-- Registers for a Counter-shaped straightline: `r6` = input base; `r10` set by `initBpfState`. -/
def counterStraightlineRegs : RegMap :=
  setReg initRegMap .br6 mmInputStart

/--
Simplified E1 evaluator: run the materialize+reload prefix under `step`, then reuse
`evalCheckedCFGWrite` with the resulting `r1`/`r2` contents.
-/
def evalCounterStraightline (kind : Core.CheckedArith)
    (success overflow : Core.CFG.BlockId) (store : BpfInstruction)
    (lhs rhs : OperandSource) (memory : Mem) :
    Option CheckedCFGWriteOutcome := do
  let left ← materializeOperand? lhs lhsStackOffset
  let right ← materializeOperand? rhs rhsStackOffset
  let materializePrefix := left ++ right ++ reloadOperands
  let state0 := initBpfState counterStraightlineRegs memory 64 version
  let after := runDecodedFrom 0 materializePrefix state0
  match after with
  | .ok _ regs mem _ _ _ _ _ =>
      evalCheckedCFGWrite (checkedControlFragment kind success overflow store)
        (regs .br1) (regs .br2) mem
  | .success _ | .eflag | .err => none

/-- Counter field+arg materialization and straightline assembly are well-formed. -/
theorem materializeOperand_field_arg_verified :
    (materializeOperand? (.field counterValueOffset) lhsStackOffset).isSome = true ∧
    (materializeOperand? (.arg counterArg0Offset) rhsStackOffset).isSome = true ∧
    (staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }).isSome = true ∧
    (Option.isSome <| do
        let store ← staticStoreInstruction?
          { name := "value", offset := 8, width := 8, abi := "u64-le" }
        checkedStraightlineFragment? .add 11 12 store
          (.field counterValueOffset) (.arg counterArg0Offset)) = true := by
  native_decide

/-- Literal RHS materialization also builds a verified straightline. -/
theorem materializeOperand_field_lit_verified :
    (materializeOperand? (.lit 5) rhsStackOffset).isSome = true ∧
    (Option.isSome <| do
        let store ← staticStoreInstruction?
          { name := "value", offset := 8, width := 8, abi := "u64-le" }
        checkedStraightlineFragment? .add 11 12 store
          (.field counterValueOffset) (.lit 5)) = true := by
  native_decide

/-- Concrete Counter add (7+5) through materialize → E0 success writes 12. -/
theorem evalCounterStraightline_add_7_5 :
    (do
      let mem ← counterInputMem 7 5
      let store ← staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
      let outcome ← evalCounterStraightline .add 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset) mem
      match outcome with
      | .success target finalMem =>
          pure (target == 11 &&
            loadv .m64 finalMem (mmInputStart + 104) == some (.vlong 12))
      | .overflow _ _ => pure false) = some true := by
  native_decide

/-- Concrete Counter overflow (max+1) through materialize → E0 overflow, value unchanged. -/
theorem evalCounterStraightline_add_overflow_max :
    (do
      let mem ← counterInputMem (~~~(0 : U64)) 1
      let store ← staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
      let before := loadv .m64 mem (mmInputStart + 104)
      let outcome ← evalCounterStraightline .add 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset) mem
      match outcome with
      | .overflow target finalMem =>
          pure (target == 12 && loadv .m64 finalMem (mmInputStart + 104) == before)
      | .success _ _ => pure false) = some true := by
  native_decide

/-! ## E3 — Counter increment multi-block CFG (`svm-sem-003`)

Whole-function bounded CFG for Counter `increment` matching the emit layout:

* **entry** — materialize operands, checked-add guard, ALU, scratch `[r10-24]`, `ja` edge
* **success** — reload scratch, account store, `r0 = 0`, `exit`
* **overflow** — `r0 = 0x1001`, `exit` (no account store)

E1 inlines the store into the guard fallthrough; E3 restores the CFG split used by
`Emit.checkedCFGTemplate` + success/overflow exits. Bounds: ≤ 3 blocks, ≤ 64 entry+exit
instructions, fuel 64. Still out of scope at E3: walked `r7` args, Agave/ELF. AccountWords bridge is E4.
-/

/-- Official SVM overflow exit code used by `Emit.emitOverflowReturn` (`0x1001`). -/
def overflowReturnCode : U32 := 0x1001

/-- Explicit CFG block bound for Counter `increment` (entry + success + overflow). -/
def counterIncrementBlockBound : Nat := 3

/-- Instruction budget covering entry materialize/guard/tail plus both exit blocks. -/
def counterIncrementInstrBound : Nat := 64

/-- Add guard whose overflow edge skips the 4-instruction entry tail (ALU + scratch + `ja`). -/
def counterIncrementAddGuard : EbpfAsm :=
  [ .ldImm .br3 0xffffffff 0xffffffff,
    .alu64 .sub .br3 (.reg .br2),
    .jump .gt .br1 (.reg .br3) 4 ]

/-- Local PC after a successful add guard (same slot count as E0 add). -/
def counterIncrementSuccessPC : U64 := 4

/-- Local PC of the overflow edge (= success PC + 4-instruction entry tail). -/
def counterIncrementOverflowPC : U64 := 8

/-- Entry-block tail after a successful guard: ALU, scratch handoff, CFG edge. -/
def counterIncrementEntryTail : EbpfAsm :=
  checkedArithBody .add ++
    [ .st .m64 .br10 (.reg .br4) checkedResultOffset,
      .ja 0 ]

/-- Success successor: reload scratch, account store, return 0, exit. -/
def counterIncrementSuccessBlock (store : BpfInstruction) : EbpfAsm :=
  [ .ldx .m64 .br1 .br10 checkedResultOffset,
    store,
    .ldImm .br0 0 0 ]

/-- Overflow successor: return `0x1001`, exit. No account store. -/
def counterIncrementOverflowBlock : EbpfAsm :=
  [ .ldImm .br0 overflowReturnCode 0 ]

/-- Typed multi-block fragment for Counter `increment`. -/
structure CounterIncrementCFG where
  success : Core.CFG.BlockId
  overflow : Core.CFG.BlockId
  entry : EbpfAsm
  successBlock : EbpfAsm
  overflowBlock : EbpfAsm
  deriving Repr, BEq

/-- Assemble the three-block Counter increment CFG from operand sources and a static store. -/
def counterIncrementCFG? (success overflow : Core.CFG.BlockId) (store : BpfInstruction)
    (lhs rhs : OperandSource) : Option CounterIncrementCFG := do
  let left ← materializeOperand? lhs lhsStackOffset
  let right ← materializeOperand? rhs rhsStackOffset
  let entry :=
    left ++ right ++ reloadOperands ++ counterIncrementAddGuard ++ counterIncrementEntryTail
  let successBlock := counterIncrementSuccessBlock store
  let overflowBlock := counterIncrementOverflowBlock
  if entry.length + successBlock.length + overflowBlock.length > counterIncrementInstrBound then
    none
  else
    some {
      success
      overflow
      entry
      successBlock
      overflowBlock
    }

/-- Outcome of the multi-block Counter increment CFG, including the exit `r0` convention. -/
inductive CounterIncrementOutcome where
  | success (target : Core.CFG.BlockId) (memory : Mem) (r0 : U64)
  | overflow (target : Core.CFG.BlockId) (memory : Mem) (r0 : U64)

/--
Structured E3 evaluator: materialize, run add-guard, then dispatch to entry-tail+success
or overflow exit. Mirrors `Emit.checkedCFGTemplate` edge selection without flattening the
account store into the guard fallthrough.
-/
def evalCounterIncrementCFG (success overflow : Core.CFG.BlockId) (store : BpfInstruction)
    (lhs rhs : OperandSource) (memory : Mem) : Option CounterIncrementOutcome := do
  let left ← materializeOperand? lhs lhsStackOffset
  let right ← materializeOperand? rhs rhsStackOffset
  let materializePrefix := left ++ right ++ reloadOperands
  let state0 := initBpfState counterStraightlineRegs memory 64 version
  match runDecodedFrom 0 materializePrefix state0 with
  | .ok _ regs mem _ _ _ _ _ =>
      let guardState := initBpfState regs mem 64 version
      let guarded := runDecodedFrom 0 counterIncrementAddGuard guardState
      match guarded with
      | .ok pc _ _ _ _ _ _ _ =>
          if pc == counterIncrementSuccessPC then
            match runDecodedFrom counterIncrementSuccessPC.toNat counterIncrementEntryTail
                guarded with
            | .ok _ tailRegs tailMem _ _ _ _ _ =>
                let successState := initBpfState tailRegs tailMem 64 version
                match runDecodedFrom 0 (counterIncrementSuccessBlock store) successState with
                | .ok _ finalRegs finalMem _ _ _ _ _ =>
                    some (.success success finalMem (finalRegs .br0))
                | .success _ | .eflag | .err => none
            | .success _ | .eflag | .err => none
          else if pc == counterIncrementOverflowPC then
            match guarded with
            | .ok _ ovRegs ovMem _ _ _ _ _ =>
                let overflowState := initBpfState ovRegs ovMem 64 version
                match runDecodedFrom 0 counterIncrementOverflowBlock overflowState with
                | .ok _ finalRegs finalMem _ _ _ _ _ =>
                    some (.overflow overflow finalMem (finalRegs .br0))
                | .success _ | .eflag | .err => none
            | _ => none
          else none
      | .success _ | .eflag | .err => none
  | .success _ | .eflag | .err => none

/-- The three-block Counter increment CFG stays inside the declared instruction budget. -/
theorem counterIncrementCFG_within_bounds :
    (do
      let store ← staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
      let cfg ← counterIncrementCFG? 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset)
      pure (cfg.entry.length + cfg.successBlock.length + cfg.overflowBlock.length ≤
        counterIncrementInstrBound ∧ counterIncrementBlockBound = 3)) = some true := by
  native_decide

/-- Concrete success path: 7+5 writes 12, returns `r0 = 0`, lands on the success block id. -/
theorem evalCounterIncrementCFG_add_7_5 :
    (do
      let mem ← counterInputMem 7 5
      let store ← staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
      let outcome ← evalCounterIncrementCFG 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset) mem
      match outcome with
      | .success target finalMem r0 =>
          pure (target == 11 && r0 == 0 &&
            loadv .m64 finalMem (mmInputStart + 104) == some (.vlong 12))
      | .overflow _ _ _ => pure false) = some true := by
  native_decide

/-- Concrete overflow path: max+1 leaves value unchanged and returns `r0 = 0x1001`. -/
theorem evalCounterIncrementCFG_overflow_max :
    (do
      let mem ← counterInputMem (~~~(0 : U64)) 1
      let store ← staticStoreInstruction?
        { name := "value", offset := 8, width := 8, abi := "u64-le" }
      let before := loadv .m64 mem (mmInputStart + 104)
      let outcome ← evalCounterIncrementCFG 11 12 store
        (.field counterValueOffset) (.arg counterArg0Offset) mem
      match outcome with
      | .overflow target finalMem r0 =>
          pure (target == 12 && r0 == BitVec.ofNat 64 overflowReturnCode.toNat &&
            loadv .m64 finalMem (mmInputStart + 104) == before)
      | .success _ _ _ => pure false) = some true := by
  native_decide


/-! ## E4 — AccountWords ↔ typed storev/loadv (`svm-sem-004`)

Bridge Track A `AccountWords` field writes to Solanalib `storev`/`loadv` on **bounded
account-data slots only**. Knife layout: Counter `value` = account-data word 1
(`ACC0_DATA + 8` = 104). Arbitrary VAs, heap bump, and CPI visibility stay out of scope.
-/

open ProofForge.Svm.Sdk.StorageModel
open ProofForge.Svm.AccountStorage

/-- Byte offset of account-data word `w` from the Loader input base. -/
def accountWordByteOffset (w : Nat) : Nat :=
  ABI.acc0Data + w * 8

/-- Absolute Solanalib address of account-data word `w`. -/
def accountWordAddr (w : Nat) : U64 :=
  mmInputStart + BitVec.ofNat 64 (accountWordByteOffset w)

/-- Emitter static-offset budget: `stxdw [r6 + off]` uses a signed 16-bit displacement. -/
def accountWordInStaticRange (w : Nat) : Bool :=
  decide (accountWordByteOffset w < 2 ^ 15)

/-- Counter `value` occupies account-data word 1 (discriminator at word 0). -/
def counterValueWord : Nat := 1

/-- Track A scalar field for Counter `value` on account 0. -/
def counterValueField : Field :=
  Field.scalar 0 counterValueWord

/-- Spec-facing projection of `mFieldWord counterValueField 0`. -/
def counterValueFieldWord? : Option Nat :=
  mFieldWord counterValueField 0

/-- `AccountWords` uses `UInt64`; Solanalib memory uses `U64`. -/
def u64OfAccountWord (v : UInt64) : U64 :=
  BitVec.ofNat 64 v.toNat

def accountWordOfU64 (v : U64) : UInt64 :=
  UInt64.ofNat v.toNat

/-- Typed store of one aligned account word; fail-closed outside the static offset budget. -/
def storeAccountWord? (memory : Mem) (w : Nat) (v : U64) : Option Mem :=
  if accountWordInStaticRange w then
    storev .m64 memory (accountWordAddr w) (.vlong v)
  else
    none

/-- Typed load of one aligned account word; fail-closed on OOB range or unmapped bytes. -/
def loadAccountWord? (memory : Mem) (w : Nat) : Option U64 :=
  if !accountWordInStaticRange w then none
  else
    match loadv .m64 memory (accountWordAddr w) with
    | some (.vlong v) => some v
    | _ => none

/-- Project one `AccountWords` slot into Solanalib memory. -/
def projectAccountWord? (aw : AccountWords) (w : Nat) (memory : Mem := initMem) :
    Option Mem :=
  storeAccountWord? memory w (u64OfAccountWord (aw w))

/-- Model field write then project the target word (fail-closed when the field index is OOB). -/
def projectFieldWrite? (aw : AccountWords) (f : Field) (index : UInt64) (v : UInt64)
    (memory : Mem := initMem) : Option Mem :=
  match mFieldWord f index with
  | none => none
  | some w => projectAccountWord? (mWriteField aw f index v) w memory

/-- Counter value word maps to the same absolute offset used by E0–E3. -/
theorem counterValueWord_offset :
    accountWordByteOffset counterValueWord = counterValueOffset ∧
      counterValueOffset = 104 := by
  native_decide

/-- Track A resolves Counter `value` to account-data word 1. -/
theorem mFieldWord_counterValue :
    mFieldWord counterValueField 0 = some counterValueWord := by
  native_decide

/-- Typed store then load round-trips on the Counter value word. -/
theorem storeAccountWord_load_roundtrip :
    (do
      let m ← storeAccountWord? initMem counterValueWord 42
      loadAccountWord? m counterValueWord) = some 42 := by
  native_decide

/-- Unmapped Counter value word fails closed under typed load. -/
theorem loadAccountWord_unmapped :
    (loadAccountWord? initMem counterValueWord).isNone = true := by
  native_decide

/-- Word indexes whose byte offset exits the signed-16 static budget fail closed. -/
theorem storeAccountWord_oob_static :
    (storeAccountWord? initMem 4084 1).isNone = true ∧
      (loadAccountWord? initMem 4084).isNone = true := by
  native_decide

/-- OOB scalar field index fails closed at the bridge (model write is a no-op). -/
theorem projectFieldWrite_oob_index :
    (projectFieldWrite? (fun _ => 0) counterValueField 1 (accountWordOfU64 7)).isNone =
      true := by
  native_decide

/-- Model field write + project equals a direct typed `storev` of the same word
(observable at the Counter value slot). -/
theorem projectFieldWrite_eq_storeAccountWord :
    (do
      let viaModel ←
        projectFieldWrite? (fun _ => 0) counterValueField 0 (accountWordOfU64 42)
      let viaStore ← storeAccountWord? initMem counterValueWord 42
      let a ← loadAccountWord? viaModel counterValueWord
      let b ← loadAccountWord? viaStore counterValueWord
      pure (a == b && a == 42)) = some true := by
  native_decide

/-- After a model write, `mReadField` agrees with typed `loadv` on the projected memory. -/
theorem mReadField_matches_loadAccountWord :
    (do
      let aw0 : AccountWords := fun _ => 0
      let aw1 := mWriteField aw0 counterValueField 0 (accountWordOfU64 42)
      let mem ← projectAccountWord? aw1 counterValueWord
      let loaded ← loadAccountWord? mem counterValueWord
      pure (loaded == u64OfAccountWord (mReadField aw1 counterValueField 0) &&
        loaded == 42)) = some true := by
  native_decide

/-- Emitter-shaped static store through `evalStaticStore?` matches the AccountWords bridge
(observable at the Counter value slot). -/
theorem storeAccountWord_eq_evalStaticStore :
    (do
      let regs := setReg (setReg initRegMap .br6 mmInputStart) .br1 42
      let viaStatic ← evalStaticStore?
        { name := "value", offset := 8, width := 8, abi := "u64-le" } regs initMem
      let viaBridge ← storeAccountWord? initMem counterValueWord 42
      let a ← loadAccountWord? viaStatic counterValueWord
      let b ← loadAccountWord? viaBridge counterValueWord
      pure (a == b && a == 42)) = some true := by
  native_decide


/-! ## E5 — BoundedQueue empty-push L3 correspondence (`svm-sem-005`)

Same Track A subject as `sf-001`/`sf-002`: `BoundedQueue` / `mQueuePush`.
Covers the **empty-push** path only (head = 0, count = 0 → three account-word
writes) projected through the E4 `storev`/`loadv` bridge. Layout knife matches
`Examples.TicketLine` (head@2, count@3, slots@4, capacity 16).

Still out of L3: full / nowrap / wrap push; all pop / peek / initialize branches;
whole-program TicketLine emit→step; Agave Loader/syscall/ELF host (beyond the E∞
walked-`r7` knife below).
-/

open ProofForge.Svm.Sdk.Queue

/-- TicketLine-shaped queue on account 1: head@2, count@3, slots@4..19. -/
def demoQueue : BoundedQueue :=
  BoundedQueue.oneBased 1 2 4 16

def demoQueueHeadWord : Nat := 2
def demoQueueCountWord : Nat := 3
def demoQueueSlot1Word : Nat := 4

theorem demoQueue_wellFormed :
    demoQueue.wellFormed = true := by
  native_decide

theorem demoQueue_fieldWords :
    mFieldWord demoQueue.head 0 = some demoQueueHeadWord ∧
      mFieldWord demoQueue.count 0 = some demoQueueCountWord ∧
        mFieldWord demoQueue.slots 1 = some demoQueueSlot1Word := by
  native_decide

/-- Spec-facing field-word projections for the demo queue. -/
def demoQueueHeadWord? : Option Nat := mFieldWord demoQueue.head 0
def demoQueueCountWord? : Option Nat := mFieldWord demoQueue.count 0
def demoQueueSlot1Word? : Option Nat := mFieldWord demoQueue.slots 1

theorem demoQueue_words_in_static_range :
    accountWordInStaticRange demoQueueHeadWord = true ∧
      accountWordInStaticRange demoQueueCountWord = true ∧
        accountWordInStaticRange demoQueueSlot1Word = true := by
  native_decide

/-- Zeroed AccountWords: empty queue headers and empty slots. -/
def emptyAccountWords : AccountWords := fun _ => 0

/-- Model memory after empty-push of `value`. -/
def demoEmptyPushAw (value : UInt64) : AccountWords :=
  (mQueuePush emptyAccountWords demoQueue value).1

/-- Spec-facing model readbacks after empty-push of `value`. -/
def demoEmptyPushCount (value : UInt64) : UInt64 :=
  mReadField (demoEmptyPushAw value) demoQueue.count 0
def demoEmptyPushHead (value : UInt64) : UInt64 :=
  mReadField (demoEmptyPushAw value) demoQueue.head 0
def demoEmptyPushSlot1 (value : UInt64) : UInt64 :=
  mReadField (demoEmptyPushAw value) demoQueue.slots 1

/-- Project the three empty-push writes into Solanalib Mem via the E4 bridge. -/
def projectDemoEmptyPush? (value : U64) : Option Mem := do
  let aw := demoEmptyPushAw (accountWordOfU64 value)
  let m0 ← projectAccountWord? aw demoQueueSlot1Word initMem
  let m1 ← projectAccountWord? aw demoQueueHeadWord m0
  projectAccountWord? aw demoQueueCountWord m1

/-- Typed three-store sequence with the same write set as empty-push. -/
def demoEmptyPushStores? (value : U64) : Option Mem := do
  let m0 ← storeAccountWord? initMem demoQueueSlot1Word value
  let m1 ← storeAccountWord? m0 demoQueueHeadWord 1
  storeAccountWord? m1 demoQueueCountWord 1

/-- L2 empty-push readback on the demo layout (count/head/slot1). -/
theorem demoEmptyPush_model_readback :
    (let aw := demoEmptyPushAw (accountWordOfU64 42);
      mReadField aw demoQueue.count 0 == (1 : UInt64) &&
        mReadField aw demoQueue.head 0 == (1 : UInt64) &&
          mReadField aw demoQueue.slots 1 == accountWordOfU64 42) = true := by
  native_decide

/-- Projected Solanalib loads match the empty-push model write set. -/
theorem projectDemoEmptyPush_loads :
    (do
      let mem ← projectDemoEmptyPush? 42
      let slot ← loadAccountWord? mem demoQueueSlot1Word
      let head ← loadAccountWord? mem demoQueueHeadWord
      let count ← loadAccountWord? mem demoQueueCountWord
      pure (slot == 42 && head == 1 && count == 1)) = some true := by
  native_decide

/-- Direct typed stores of the empty-push write set load back the same words. -/
theorem demoEmptyPushStores_loads :
    (do
      let mem ← demoEmptyPushStores? 42
      let slot ← loadAccountWord? mem demoQueueSlot1Word
      let head ← loadAccountWord? mem demoQueueHeadWord
      let count ← loadAccountWord? mem demoQueueCountWord
      pure (slot == 42 && head == 1 && count == 1)) = some true := by
  native_decide

/-- Model projection and typed three-store path agree on the empty-push write set. -/
theorem projectDemoEmptyPush_eq_stores :
    (do
      let viaModel ← projectDemoEmptyPush? 42
      let viaStores ← demoEmptyPushStores? 42
      let s1 ← loadAccountWord? viaModel demoQueueSlot1Word
      let s2 ← loadAccountWord? viaStores demoQueueSlot1Word
      let h1 ← loadAccountWord? viaModel demoQueueHeadWord
      let h2 ← loadAccountWord? viaStores demoQueueHeadWord
      let c1 ← loadAccountWord? viaModel demoQueueCountWord
      let c2 ← loadAccountWord? viaStores demoQueueCountWord
      pure (s1 == s2 && h1 == h2 && c1 == c2 &&
        s1 == 42 && h1 == 1 && c1 == 1)) = some true := by
  native_decide

/-!
## E-infinity knife - walked r7 instruction-data cursor (svm-sem-006)

EntryAdapter / raw Borsh paths keep a walking instruction-data cursor in r7
(ldxdw / width advance) rather than only absolute [r6 + INSTRUCTION_DATA + off]
loads. This first host-adequacy knife materializes one Counter-shaped arg0 through
that cursor and proves it agrees with E1 absolute arg materialization on the
staged stack word. Still far from Loader serialization, syscalls, CPI, or ELF accept.
-/

/-- Typed counterpart of ldxdw r1,[r7+0]; add64 r7,8; stxdw [r10+stackOff],r1. -/
def walkArgU64? (stackOff : U16) : Option EbpfAsm := do
  let off ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br7 off,
    .alu64 .add .br7 (.imm 8),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- `r6` = input base; `r7` = absolute Counter arg0 cursor (same byte as E1 `.arg`). -/
def counterWalkedArgRegs : RegMap :=
  setReg (setReg initRegMap .br6 mmInputStart)
    .br7 (mmInputStart + BitVec.ofNat 64 counterArg0Offset)

/-- Canonical sBPF frame pointer installed by `initBpfState`. -/
def counterFramePointer : U64 :=
  mmStackStart + stackFrameSize * maxCallDepth

/-- Absolute address of the RHS staged stack slot (`[r10 - 16]`). -/
def rhsStackAddr : U64 :=
  counterFramePointer - 16

/-- Run the walked-`r7` arg load against seeded Counter input memory. -/
def evalWalkArgToStack? (stackOff : U16) (memory : Mem) : Option (RegMap × Mem) := do
  let frag ← walkArgU64? stackOff
  let state0 := initBpfState counterWalkedArgRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute E1 materialize of Counter arg0 into the RHS stack slot. -/
def evalAbsArgToStack? (memory : Mem) : Option (RegMap × Mem) := do
  let frag ← materializeOperand? (.arg counterArg0Offset) rhsStackOffset
  let state0 := initBpfState counterStraightlineRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Walked-`r7` assembly is well-formed. -/
theorem walkArgU64_verified :
    (walkArgU64? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walked load of arg0 (=5) leaves 5 in `r1`, stages it at `[r10-16]`, and advances `r7`. -/
theorem evalWalkArg_arg0_5 :
    (do
      let mem ← counterInputMem 7 5
      let (regs, finalMem) ← evalWalkArgToStack? rhsStackOffset mem
      pure (regs .br1 == 5 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 5) &&
        regs .br7 == mmInputStart + BitVec.ofNat 64 (counterArg0Offset + 8))) =
      some true := by
  native_decide

/-- Walked `r7` arg0 and absolute E1 `.arg` materialization agree on the staged stack word. -/
theorem walkArg_eq_absArg_stack :
    (do
      let mem ← counterInputMem 7 5
      let (_, walkedMem) ← evalWalkArgToStack? rhsStackOffset mem
      let (_, absMem) ← evalAbsArgToStack? mem
      pure (loadv .m64 walkedMem rhsStackAddr == loadv .m64 absMem rhsStackAddr &&
        loadv .m64 walkedMem rhsStackAddr == some (.vlong 5))) =
      some true := by
  native_decide

/-!
## E-infinity knife 2 - two consecutive walked `r7` args (`svm-sem-007`)

EntryAdapter Borsh decode walks multiple fields through the same cursor. This second
host knife stages arg0 then arg1 via two `walkArgU64?` steps and proves each staged
word matches absolute E1 `.arg` materialization, with `r7` advanced by 16. Still not
Loader/syscall/CPI/ELF.
-/

/-- Absolute input-region offset of a second Counter-shaped u64 arg (arg0 + 8). -/
def counterArg1Offset : Nat := counterArg0Offset + 8

/-- Absolute address of the LHS staged stack slot (`[r10 - 8]`). -/
def lhsStackAddr : U64 :=
  counterFramePointer - 8

/-- Seed Loader input memory with Counter `value`, arg0, and arg1 words. -/
def counterInputMem2 (value arg0 arg1 : U64) : Option Mem := do
  let m₁ ← counterInputMem value arg0
  storev .m64 m₁ (mmInputStart + BitVec.ofNat 64 counterArg1Offset) (.vlong arg1)

/-- Walk arg0 into RHS then arg1 into LHS through the shared `r7` cursor. -/
def evalWalkTwoArgsToStack? (memory : Mem) : Option (RegMap × Mem) := do
  let frag0 ← walkArgU64? rhsStackOffset
  let frag1 ← walkArgU64? lhsStackOffset
  let state0 := initBpfState counterWalkedArgRegs memory 64 version
  let after := runDecodedFrom 0 (frag0 ++ frag1) state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute E1 materialize of Counter arg1 into the LHS stack slot. -/
def evalAbsArg1ToStack? (memory : Mem) : Option (RegMap × Mem) := do
  let frag ← materializeOperand? (.arg counterArg1Offset) lhsStackOffset
  let state0 := initBpfState counterStraightlineRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Concrete two-arg walk: arg0=5 / arg1=9 stage correctly and advance `r7` by 16. -/
theorem evalWalkTwoArgs_arg0_5_arg1_9 :
    (do
      let mem ← counterInputMem2 7 5 9
      let (regs, finalMem) ← evalWalkTwoArgsToStack? mem
      pure (loadv .m64 finalMem rhsStackAddr == some (.vlong 5) &&
        loadv .m64 finalMem lhsStackAddr == some (.vlong 9) &&
        regs .br1 == 9 &&
        regs .br7 == mmInputStart + BitVec.ofNat 64 (counterArg0Offset + 16))) =
      some true := by
  native_decide

/-- Walked two-arg pipeline agrees with absolute E1 `.arg` materialization on both staged words. -/
theorem walkTwoArgs_eq_absArgs_stack :
    (do
      let mem ← counterInputMem2 7 5 9
      let (_, walkedMem) ← evalWalkTwoArgsToStack? mem
      let (_, abs0Mem) ← evalAbsArgToStack? mem
      let (_, abs1Mem) ← evalAbsArg1ToStack? mem
      pure (loadv .m64 walkedMem rhsStackAddr == loadv .m64 abs0Mem rhsStackAddr &&
        loadv .m64 walkedMem lhsStackAddr == loadv .m64 abs1Mem lhsStackAddr &&
        loadv .m64 walkedMem rhsStackAddr == some (.vlong 5) &&
        loadv .m64 walkedMem lhsStackAddr == some (.vlong 9))) =
      some true := by
  native_decide

end ProofForge.Svm.Solanalib
