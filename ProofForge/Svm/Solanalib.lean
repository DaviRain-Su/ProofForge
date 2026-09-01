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

/-!
## E-infinity knife 3 - Loader account-0 header/key walk (`svm-sem-008`)

Loader-v3 serializes account 0 at `ACC0_HEADER` (`0x8`): dup marker, signer/writable flags,
then `ACC0_KEY` (`0x10`). This host knife walks a cursor in `r8` over that header, loads the
non-dup marker byte and the first pubkey limb, and proves agreement with absolute `r6`-relative
loads. Still not full account vector walk, syscalls, CPI, or ELF accept.
-/

/-- Absolute input offsets matching `Emit` `.equ ACC0_HEADER` / `ACC0_KEY`. -/
def account0HeaderOffset : Nat := 0x8
def account0KeyOffset : Nat := 0x10
def account0NonDupMarker : U8 := 0xff

/-- Absolute VAs for account-0 header byte and first key limb. -/
def account0HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0HeaderOffset
def account0KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0KeyOffset

/-- Seed Loader input with Counter value/arg0 plus account-0 non-dup header and key limb. -/
def account0MetaInputMem (value arg0 keyLimb : U64) : Option Mem := do
  let m₁ ← counterInputMem value arg0
  let m₂ ← storev .m8 m₁ account0HeaderAddr (.vbyte account0NonDupMarker)
  storev .m64 m₂ account0KeyAddr (.vlong keyLimb)

/-- `r6` = input base; `r8` = absolute account-0 header cursor (`ACC0_HEADER`). -/
def account0WalkRegs : RegMap :=
  setReg (setReg initRegMap .br6 mmInputStart)
    .br8 (mmInputStart + BitVec.ofNat 64 account0HeaderOffset)

/-- Typed walk: ldxb r1,[r8+0]; ldxdw r2,[r8+8]; stxdw [r10+stackOff],r2. -/
def walkAccount0Meta? (stackOff : U16) : Option EbpfAsm := do
  let dupOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m8 .br1 .br8 dupOff,
    .ldx .m64 .br2 .br8 keyOff,
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run the walked account-0 meta load against seeded input memory. -/
def evalWalkAccount0MetaToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0Meta? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 dup byte and key limb. -/
def evalAbsAccount0Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account0HeaderAddr
  let key ← loadv .m64 memory account0KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-0 assembly is well-formed. -/
theorem walkAccount0Meta_verified :
    (walkAccount0Meta? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: dup=`0xff`, key limb=`0x42`, staged at `[r10-16]`. -/
theorem evalWalkAccount0_key_0x42 :
    (do
      let mem ← account0MetaInputMem 7 5 0x42
      let (regs, finalMem) ← evalWalkAccount0MetaToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x42 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x42))) =
      some true := by
  native_decide

/-- Walked account-0 meta agrees with absolute `r6`-relative header/key loads. -/
theorem walkAccount0Meta_eq_absLoad :
    (do
      let mem ← account0MetaInputMem 7 5 0x42
      let (regs, _) ← evalWalkAccount0MetaToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount0Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == account0NonDupMarker && key == 0x42)) =
      some true := by
  native_decide

/-!
## E-infinity knife 4 - Loader account-0 signer/writable flags (`svm-sem-009`)

Emit gates account-0 with `ldxb` of `ACC0_HEADER+1` (signer) and `+2` (writable). This knife
walks those two flag bytes through the same `r8` header cursor and proves agreement with absolute
`r6`-relative loads. Still not owner/lamports/data_len, full account vector, syscalls, or ELF accept.
-/

/-- Absolute VAs for account-0 signer and writable flag bytes. -/
def account0SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account0HeaderOffset + 1)
def account0WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account0HeaderOffset + 2)

/-- Seed Loader input with account-0 non-dup header, signer/writable flags, and key limb. -/
def account0FlagsInputMem (value arg0 keyLimb : U64) (signer writable : U8) : Option Mem := do
  let m₁ ← account0MetaInputMem value arg0 keyLimb
  let m₂ ← storev .m8 m₁ account0SignerAddr (.vbyte signer)
  storev .m8 m₂ account0WritableAddr (.vbyte writable)

/-- Typed walk: ldxb r1,[r8+1]; ldxb r2,[r8+2]; stxdw [r10+stackOff],r1. -/
def walkAccount0Flags? (stackOff : U16) : Option EbpfAsm := do
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m8 .br1 .br8 signerOff,
    .ldx .m8 .br2 .br8 writableOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0 flag load against seeded input memory. -/
def evalWalkAccount0FlagsToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0Flags? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 signer and writable flag bytes. -/
def evalAbsAccount0Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account0SignerAddr
  let writable ← loadv .m8 memory account0WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-0 flag assembly is well-formed. -/
theorem walkAccount0Flags_verified :
    (walkAccount0Flags? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount0_signer_writable_1 :
    (do
      let mem ← account0FlagsInputMem 7 5 0x42 1 1
      let (regs, finalMem) ← evalWalkAccount0FlagsToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-0 flags agree with absolute `r6`-relative header loads. -/
theorem walkAccount0Flags_eq_absLoad :
    (do
      let mem ← account0FlagsInputMem 7 5 0x42 1 0
      let (regs, _) ← evalWalkAccount0FlagsToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount0Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide


/-!
## E-infinity knife 5 - Loader account-0 lamports/data_len (`svm-sem-010`)

Emit loads account-0 `ACC0_LAMPORTS` (`0x50`) and `ACC0_DATA_LEN` (`0x58`) as absolute
`r6`-relative u64 words. This knife walks those two fields from the same `r8` header cursor
(`ACC0_HEADER`) and proves agreement with absolute loads. Still not owner limbs, full account
vector, syscalls, CPI, or ELF accept.
-/

/-- Absolute input offsets matching `Emit` `.equ ACC0_LAMPORTS` / `ACC0_DATA_LEN`. -/
def account0LamportsOffset : Nat := 0x50
def account0DataLenOffset : Nat := 0x58

/-- Absolute VAs for account-0 lamports and data_len words. -/
def account0LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0LamportsOffset
def account0DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0DataLenOffset

/-- Seed Loader input with account-0 meta plus lamports and data_len words. -/
def account0BudgetInputMem (value arg0 keyLimb lamports dataLen : U64) : Option Mem := do
  let m₁ ← account0MetaInputMem value arg0 keyLimb
  let m₂ ← storev .m64 m₁ account0LamportsAddr (.vlong lamports)
  storev .m64 m₂ account0DataLenAddr (.vlong dataLen)

/-- Typed walk from header cursor: ldxdw r1,[r8+0x48]; ldxdw r2,[r8+0x50]; stxdw [r10+off],r1. -/
def walkAccount0Budget? (stackOff : U16) : Option EbpfAsm := do
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 lamportsOff,
    .ldx .m64 .br2 .br8 dataLenOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0 lamports/data_len load against seeded input memory. -/
def evalWalkAccount0BudgetToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0Budget? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 lamports and data_len. -/
def evalAbsAccount0Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account0LamportsAddr
  let dataLen ← loadv .m64 memory account0DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-0 budget assembly is well-formed. -/
theorem walkAccount0Budget_verified :
    (walkAccount0Budget? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: lamports=`1000`, data_len=`128`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount0_lamports_1000_dataLen_128 :
    (do
      let mem ← account0BudgetInputMem 7 5 0x42 1000 128
      let (regs, finalMem) ← evalWalkAccount0BudgetToStack? rhsStackOffset mem
      pure (regs .br1 == 1000 && regs .br2 == 128 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1000))) =
      some true := by
  native_decide

/-- Walked account-0 budget agrees with absolute `r6`-relative loads. -/
theorem walkAccount0Budget_eq_absLoad :
    (do
      let mem ← account0BudgetInputMem 7 5 0x42 1000 128
      let (regs, _) ← evalWalkAccount0BudgetToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount0Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 1000 && dataLen == 128)) =
      some true := by
  native_decide


/-!
## E-infinity knife 6 - Loader account-0 owner limbs (`svm-sem-011`)

Emit validates account-0 ownership via absolute `ldxdw` of `ACC0_OWNER` (`0x30`) and
`ACC0_OWNER+8`. This knife walks the first two owner limbs from the same `r8` header cursor
and proves agreement with absolute `r6`-relative loads. Still not remaining owner limbs, full
account vector, syscalls, CPI, or ELF accept.
-/

/-- Absolute input offsets matching `Emit` `.equ ACC0_OWNER` / `ACC0_OWNER+8`. -/
def account0Owner0Offset : Nat := 0x30
def account0Owner1Offset : Nat := 0x38

/-- Absolute VAs for account-0 owner limbs 0 and 1. -/
def account0Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0Owner0Offset
def account0Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0Owner1Offset

/-- Seed Loader input with account-0 meta plus the first two owner limbs. -/
def account0OwnerInputMem (value arg0 keyLimb owner0 owner1 : U64) : Option Mem := do
  let m₁ ← account0MetaInputMem value arg0 keyLimb
  let m₂ ← storev .m64 m₁ account0Owner0Addr (.vlong owner0)
  storev .m64 m₂ account0Owner1Addr (.vlong owner1)

/-- Typed walk from header cursor: ldxdw r1,[r8+0x28]; ldxdw r2,[r8+0x30]; stxdw [r10+off],r1. -/
def walkAccount0Owner? (stackOff : U16) : Option EbpfAsm := do
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 owner0Off,
    .ldx .m64 .br2 .br8 owner1Off,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0 owner-limb load against seeded input memory. -/
def evalWalkAccount0OwnerToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0Owner? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 owner limbs 0 and 1. -/
def evalAbsAccount0Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account0Owner0Addr
  let owner1 ← loadv .m64 memory account0Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-0 owner assembly is well-formed. -/
theorem walkAccount0Owner_verified :
    (walkAccount0Owner? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: owner0=`0xA1`, owner1=`0xB2`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount0_owner0_0xA1_owner1_0xB2 :
    (do
      let mem ← account0OwnerInputMem 7 5 0x42 0xA1 0xB2
      let (regs, finalMem) ← evalWalkAccount0OwnerToStack? rhsStackOffset mem
      pure (regs .br1 == 0xA1 && regs .br2 == 0xB2 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xA1))) =
      some true := by
  native_decide

/-- Walked account-0 owner limbs agree with absolute `r6`-relative loads. -/
theorem walkAccount0Owner_eq_absLoad :
    (do
      let mem ← account0OwnerInputMem 7 5 0x42 0xA1 0xB2
      let (regs, _) ← evalWalkAccount0OwnerToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount0Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xA1 && owner1 == 0xB2)) =
      some true := by
  native_decide

/-!
## E-infinity knife 7 - Loader account-0 owner limbs 2/3 (`svm-sem-012`)

Emit validates the remaining owner pubkey via absolute `ldxdw` of `ACC0_OWNER+16` (`0x40`) and
`ACC0_OWNER+24` (`0x48`). This knife walks those limbs from the same `r8` header cursor and proves
agreement with absolute `r6`-relative loads. Still not full account vector, syscalls, CPI, or ELF
accept.
-/

/-- Absolute input offsets matching `Emit` `.equ ACC0_OWNER+16` / `ACC0_OWNER+24`. -/
def account0Owner2Offset : Nat := 0x40
def account0Owner3Offset : Nat := 0x48

/-- Absolute VAs for account-0 owner limbs 2 and 3. -/
def account0Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0Owner2Offset
def account0Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0Owner3Offset

/-- Seed Loader input with account-0 meta plus owner limbs 2 and 3. -/
def account0OwnerHiInputMem (value arg0 keyLimb owner2 owner3 : U64) : Option Mem := do
  let m₁ ← account0MetaInputMem value arg0 keyLimb
  let m₂ ← storev .m64 m₁ account0Owner2Addr (.vlong owner2)
  storev .m64 m₂ account0Owner3Addr (.vlong owner3)

/-- Typed walk from header cursor: ldxdw r1,[r8+0x38]; ldxdw r2,[r8+0x40]; stxdw [r10+off],r1. -/
def walkAccount0OwnerHi? (stackOff : U16) : Option EbpfAsm := do
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 owner2Off,
    .ldx .m64 .br2 .br8 owner3Off,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0 high owner-limb load against seeded input memory. -/
def evalWalkAccount0OwnerHiToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0OwnerHi? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 owner limbs 2 and 3. -/
def evalAbsAccount0OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account0Owner2Addr
  let owner3 ← loadv .m64 memory account0Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-0 high owner assembly is well-formed. -/
theorem walkAccount0OwnerHi_verified :
    (walkAccount0OwnerHi? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: owner2=`0xC3`, owner3=`0xD4`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount0_owner2_0xC3_owner3_0xD4 :
    (do
      let mem ← account0OwnerHiInputMem 7 5 0x42 0xC3 0xD4
      let (regs, finalMem) ← evalWalkAccount0OwnerHiToStack? rhsStackOffset mem
      pure (regs .br1 == 0xC3 && regs .br2 == 0xD4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xC3))) =
      some true := by
  native_decide

/-- Walked account-0 owner limbs 2/3 agree with absolute `r6`-relative loads. -/
theorem walkAccount0OwnerHi_eq_absLoad :
    (do
      let mem ← account0OwnerHiInputMem 7 5 0x42 0xC3 0xD4
      let (regs, _) ← evalWalkAccount0OwnerHiToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount0OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0xC3 && owner3 == 0xD4)) =
      some true := by
  native_decide


/-!
## E-infinity knife 8 - Loader account-0 executable + rent_epoch (`svm-sem-013`)

Emit exposes `ACC0_HEADER+3` (executable) and `.equ ACC0_RENT_EPOCH` (layout-dependent).
For the zero-`EXACT_DATA_LEN` layout used by this knife, rent_epoch sits at absolute `0x2860`
(`ABI.inputLayoutOf 0 false _`). Walk both from the same `r8` header cursor and prove agreement
with absolute `r6`-relative loads. Still not full account vector, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets: executable byte and zero-dataLen rent_epoch word. -/
def account0ExecutableOffset : Nat := account0HeaderOffset + 3
/-- `ABI.inputLayoutOf 0 false _ |>.rentEpoch` = `0x2860`. -/
def account0RentEpochOffset : Nat := 0x2860

/-- Absolute VAs for account-0 executable flag and rent_epoch. -/
def account0ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0ExecutableOffset
def account0RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account0RentEpochOffset

/-- Seed Loader input with account-0 meta, executable flag, and rent_epoch. -/
def account0ExecRentInputMem (value arg0 keyLimb : U64) (executable : U8) (rentEpoch : U64) :
    Option Mem := do
  let m₁ ← account0MetaInputMem value arg0 keyLimb
  let m₂ ← storev .m8 m₁ account0ExecutableAddr (.vbyte executable)
  storev .m64 m₂ account0RentEpochAddr (.vlong rentEpoch)

/-- Typed walk: ldxb r1,[r8+3]; ldxdw r2,[r8+0x2858]; stxdw [r10+off],r1. -/
def walkAccount0ExecRent? (stackOff : U16) : Option EbpfAsm := do
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m8 .br1 .br8 execOff,
    .ldx .m64 .br2 .br8 rentOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0 executable/rent_epoch load against seeded input memory. -/
def evalWalkAccount0ExecRentToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0ExecRent? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-0 executable and rent_epoch. -/
def evalAbsAccount0ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account0ExecutableAddr
  let rentEpoch ← loadv .m64 memory account0RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-0 executable/rent_epoch assembly is well-formed. -/
theorem walkAccount0ExecRent_verified :
    (walkAccount0ExecRent? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete walk: executable=`1`, rent_epoch=`0xEE`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount0_executable_1_rent_0xEE :
    (do
      let mem ← account0ExecRentInputMem 7 5 0x42 1 0xEE
      let (regs, finalMem) ← evalWalkAccount0ExecRentToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-0 executable/rent_epoch agree with absolute `r6`-relative loads. -/
theorem walkAccount0ExecRent_eq_absLoad :
    (do
      let mem ← account0ExecRentInputMem 7 5 0x42 0 0xEE
      let (regs, _) ← evalWalkAccount0ExecRentToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount0ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) =
      some true := by
  native_decide


/-!
## E-infinity knife 9 - Loader account-0 → next-account marker skip (`svm-sem-014`)

Emit's account walk advances past account-0 with the PF caller geometry
`r5 = header+88+data_len+MAX_PERMITTED_DATA_INCREASE(+align8)` then reads rent and adds 8 to
reach the next dup marker (`Emit.emitSkipAccount`). For the zero-`EXACT_DATA_LEN` layout used
here that next marker sits at absolute `0x2868` (`0x8 + ABI.accountSpan 0`). This knife walks
that skip from the same `r8` header cursor and proves the loaded marker matches an absolute
`r6`-relative load. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset of the next-account dup marker after zero-dataLen rent (`0x2860+8`). -/
def account1HeaderOffset : Nat := account0RentEpochOffset + 8
/-- `Emit` `.equ MAX_PERMITTED_DATA_INCREASE`. -/
def maxPermittedDataIncrease : Nat := 0x2800
/-- Bytes from account header to the serialized data region (`Emit` add 88). -/
def accountHeaderToDataBytes : Nat := 88
/-- `ACC0_DATA_LEN` relative to `ACC0_HEADER`. -/
def account0DataLenHeaderOff : Nat := account0DataLenOffset - account0HeaderOffset

/-- Absolute VA of the next-account dup marker after a zero-dataLen account-0. -/
def account1HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1HeaderOffset

/-- Seed Loader input with account-0 meta, zero data_len, rent_epoch, and next-account marker. -/
def account0SkipNextInputMem (value arg0 keyLimb : U64) (nextMarker : U8) (rentEpoch : U64) :
    Option Mem := do
  let m₁ ← account0ExecRentInputMem value arg0 keyLimb 0 rentEpoch
  let m₂ ← storev .m64 m₁ account0DataLenAddr (.vlong 0)
  storev .m8 m₂ account1HeaderAddr (.vbyte nextMarker)

/-- Typed skip: load data_len; advance like `emitSkipAccount` (no align branch at len=0);
load next marker; stage it. -/
def walkAccount0SkipNext? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run the walked account-0→next-marker skip against seeded input memory. -/
def evalWalkAccount0SkipNextToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount0SkipNext? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the next-account dup marker. -/
def evalAbsAccount1Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account1HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-0 skip-to-next assembly is well-formed. -/
theorem walkAccount0SkipNext_verified :
    (walkAccount0SkipNext? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip: next marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount0_skip_next_marker_0xff :
    (do
      let mem ← account0SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE
      let (regs, finalMem) ← evalWalkAccount0SkipNextToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Walked next-account marker agrees with absolute `r6`-relative load after the skip. -/
theorem walkAccount0SkipNext_eq_absLoad :
    (do
      let mem ← account0SkipNextInputMem 7 5 0x42 0xAB 0xEE
      let (regs, _) ← evalWalkAccount0SkipNextToStack? rhsStackOffset mem
      let marker ← evalAbsAccount1Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) =
      some true := by
  native_decide

/-!
## E-infinity knife 10 - Loader account-1 header/key after skip (`svm-sem-015`)

Knife 9 proves the skip lands on the next dup marker. Emit then treats that address as the
account-1 header cursor (same layout as account-0: marker byte, then key at `+8`). This knife
composes the zero-`EXACT_DATA_LEN` skip with an account-1 meta load from the advanced `r2`
cursor and proves agreement with absolute `r6`-relative loads at `0x2868` / `0x2870`. Still not
a full multi-account vector walk, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-1 first key limb (`ACC1_HEADER+8` = `0x2870`). -/
def account1KeyOffset : Nat := account1HeaderOffset + 8
def account1KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1KeyOffset

/-- Seed skip layout plus account-1 first key limb. -/
def account1MetaInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) : Option Mem := do
  let m ← account0SkipNextInputMem value arg0 key0Limb nextMarker rentEpoch
  storev .m64 m account1KeyAddr (.vlong key1Limb)

/-- Typed skip then account-1 meta: after knife-9 skip, `r2` is the account-1 header;
`ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage the key. -/
def walkAccount1MetaAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run skip+account-1 meta walk against seeded input memory. -/
def evalWalkAccount1MetaAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1MetaAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 dup marker and first key limb. -/
def evalAbsAccount1Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account1HeaderAddr
  let key ← loadv .m64 memory account1KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-1-after-skip assembly is well-formed. -/
theorem walkAccount1MetaAfterSkip_verified :
    (walkAccount1MetaAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+meta: marker=`0xff`, key=`0x71`, key staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_key_0x71 :
    (do
      let mem ← account1MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71
      let (regs, finalMem) ← evalWalkAccount1MetaAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x71 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x71))) =
      some true := by
  native_decide

/-- Walked account-1 meta after skip agrees with absolute `r6`-relative loads. -/
theorem walkAccount1MetaAfterSkip_eq_absLoad :
    (do
      let mem ← account1MetaInputMem 7 5 0x42 0xAB 0xEE 0x71
      let (regs, _) ← evalWalkAccount1MetaAfterSkipToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount1Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAB && key == 0x71)) =
      some true := by
  native_decide

/-!
## E-infinity knife 11 - Loader account-1 signer/writable flags after skip (`svm-sem-016`)

Knife 10 lands the cursor on account-1 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable), same as account-0. This knife composes the zero-`EXACT_DATA_LEN` skip with
those flag loads from the advanced `r2` cursor and proves agreement with absolute `r6`-relative
loads at `0x2869` / `0x286a`. Still not lamports/owner/data_len for account-1, full vectors,
syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-1 signer and writable flag bytes. -/
def account1SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account1HeaderOffset + 1)
def account1WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account1HeaderOffset + 2)

/-- Seed skip+account-1 meta layout plus signer/writable flags. -/
def account1FlagsInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) (signer writable : U8) : Option Mem := do
  let m₁ ← account1MetaInputMem value arg0 key0Limb nextMarker rentEpoch key1Limb
  let m₂ ← storev .m8 m₁ account1SignerAddr (.vbyte signer)
  storev .m8 m₂ account1WritableAddr (.vbyte writable)

/-- Typed skip then account-1 flags: after knife-9 skip, `r2` is the account-1 header;
`ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount1FlagsAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run skip+account-1 flag walk against seeded input memory. -/
def evalWalkAccount1FlagsAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1FlagsAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 signer and writable flag bytes. -/
def evalAbsAccount1Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account1SignerAddr
  let writable ← loadv .m8 memory account1WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-1-flags-after-skip assembly is well-formed. -/
theorem walkAccount1FlagsAfterSkip_verified :
    (walkAccount1FlagsAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_signer_writable_1 :
    (do
      let mem ← account1FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1
      let (regs, finalMem) ← evalWalkAccount1FlagsAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-1 flags after skip agree with absolute `r6`-relative loads. -/
theorem walkAccount1FlagsAfterSkip_eq_absLoad :
    (do
      let mem ← account1FlagsInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0
      let (regs, _) ← evalWalkAccount1FlagsAfterSkipToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount1Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 12 - Loader account-1 lamports/data_len after skip (`svm-sem-017`)

Knife 11 covers account-1 signer/writable after the zero-`EXACT_DATA_LEN` skip. Emit then
reads account-1 lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`),
matching account-0 budget geometry. This knife composes that skip with those word loads and
proves agreement with absolute `r6`-relative loads at `account1Header+0x48` / `+0x50`. Still not
owner/executable/rent for account-1, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-1 lamports and data_len (header-relative `+0x48` / `+0x50`). -/
def account1LamportsOffset : Nat :=
  account1HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account1DataLenOffset : Nat :=
  account1HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account1LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1LamportsOffset
def account1DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1DataLenOffset

/-- Seed skip+account-1 flags layout plus lamports and data_len words. -/
def account1BudgetInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) (signer writable : U8) (lamports dataLen : U64) : Option Mem := do
  let m₁ ← account1FlagsInputMem value arg0 key0Limb nextMarker rentEpoch key1Limb signer writable
  let m₂ ← storev .m64 m₁ account1LamportsAddr (.vlong lamports)
  storev .m64 m₂ account1DataLenAddr (.vlong dataLen)

/-- Typed skip then account-1 budget: after knife-9 skip, `r2` is the account-1 header;
`ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`; stage lamports. -/
def walkAccount1BudgetAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run skip+account-1 budget walk against seeded input memory. -/
def evalWalkAccount1BudgetAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1BudgetAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 lamports and data_len. -/
def evalAbsAccount1Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account1LamportsAddr
  let dataLen ← loadv .m64 memory account1DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-1-budget-after-skip assembly is well-formed. -/
theorem walkAccount1BudgetAfterSkip_verified :
    (walkAccount1BudgetAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+budget: lamports=`1000`, data_len=`128`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_lamports_1000_dataLen_128 :
    (do
      let mem ← account1BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
      let (regs, finalMem) ← evalWalkAccount1BudgetAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1000 && regs .br2 == 128 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1000))) =
      some true := by
  native_decide

/-- Walked account-1 budget after skip agrees with absolute `r6`-relative loads. -/
theorem walkAccount1BudgetAfterSkip_eq_absLoad :
    (do
      let mem ← account1BudgetInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128
      let (regs, _) ← evalWalkAccount1BudgetAfterSkipToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount1Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 1000 && dataLen == 128)) =
      some true := by
  native_decide

/-!
## E-infinity knife 13 - Loader account-1 owner limbs 0/1 after skip (`svm-sem-018`)

Knife 12 covers account-1 lamports/data_len after the zero-`EXACT_DATA_LEN` skip. Emit then
reads account-1 owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`),
matching account-0 owner geometry. This knife composes that skip with those word loads and
proves agreement with absolute `r6`-relative loads at `account1Header+0x28` / `+0x30`. Still not
owner limbs 2/3, executable/rent for account-1, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-1 owner limbs 0 and 1 (header-relative `+0x28` / `+0x30`). -/
def account1Owner0Offset : Nat :=
  account1HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account1Owner1Offset : Nat :=
  account1HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account1Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1Owner0Offset
def account1Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1Owner1Offset

/-- Seed skip+account-1 budget layout plus owner limbs 0 and 1. -/
def account1OwnerInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 : U64) : Option Mem := do
  let m₁ ← account1BudgetInputMem value arg0 key0Limb nextMarker rentEpoch key1Limb
      signer writable lamports dataLen
  let m₂ ← storev .m64 m₁ account1Owner0Addr (.vlong owner0)
  storev .m64 m₂ account1Owner1Addr (.vlong owner1)

/-- Typed skip then account-1 owner: after knife-9 skip, `r2` is the account-1 header;
`ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`; stage owner0. -/
def walkAccount1OwnerAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run skip+account-1 owner walk against seeded input memory. -/
def evalWalkAccount1OwnerAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1OwnerAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 owner limbs 0 and 1. -/
def evalAbsAccount1Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account1Owner0Addr
  let owner1 ← loadv .m64 memory account1Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-1-owner-after-skip assembly is well-formed. -/
theorem walkAccount1OwnerAfterSkip_verified :
    (walkAccount1OwnerAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+owner: owner0=`0xA1`, owner1=`0xB2`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_owner0_0xA1_owner1_0xB2 :
    (do
      let mem ← account1OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128 0xA1 0xB2
      let (regs, finalMem) ← evalWalkAccount1OwnerAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 0xA1 && regs .br2 == 0xB2 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xA1))) =
      some true := by
  native_decide

/-- Walked account-1 owner limbs after skip agree with absolute `r6`-relative loads. -/
theorem walkAccount1OwnerAfterSkip_eq_absLoad :
    (do
      let mem ← account1OwnerInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2
      let (regs, _) ← evalWalkAccount1OwnerAfterSkipToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount1Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xA1 && owner1 == 0xB2)) =
      some true := by
  native_decide

/-!
## E-infinity knife 14 - Loader account-1 owner limbs 2/3 after skip (`svm-sem-019`)

Knife 13 covers account-1 owner limbs 0/1 after the zero-`EXACT_DATA_LEN` skip. Emit then
reads account-1 owner limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`),
matching account-0 high-owner geometry. This knife composes that skip with those word loads and
proves agreement with absolute `r6`-relative loads. Still not executable/rent for account-1, full
vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-1 owner limbs 2 and 3 (header-relative `+0x38` / `+0x40`). -/
def account1Owner2Offset : Nat :=
  account1HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account1Owner3Offset : Nat :=
  account1HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account1Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1Owner2Offset
def account1Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1Owner3Offset

/-- Seed skip+account-1 owner layout plus owner limbs 2 and 3. -/
def account1OwnerHiInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) : Option Mem := do
  let m₁ ← account1OwnerInputMem value arg0 key0Limb nextMarker rentEpoch key1Limb
      signer writable lamports dataLen owner0 owner1
  let m₂ ← storev .m64 m₁ account1Owner2Addr (.vlong owner2)
  storev .m64 m₂ account1Owner3Addr (.vlong owner3)

/-- Typed skip then account-1 high owner: after knife-9 skip, `r2` is the account-1 header;
`ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`; stage owner2. -/
def walkAccount1OwnerHiAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run skip+account-1 high-owner walk against seeded input memory. -/
def evalWalkAccount1OwnerHiAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1OwnerHiAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 owner limbs 2 and 3. -/
def evalAbsAccount1OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account1Owner2Addr
  let owner3 ← loadv .m64 memory account1Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-1-high-owner-after-skip assembly is well-formed. -/
theorem walkAccount1OwnerHiAfterSkip_verified :
    (walkAccount1OwnerHiAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+high-owner: owner2=`0xC3`, owner3=`0xD4`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_owner2_0xC3_owner3_0xD4 :
    (do
      let mem ← account1OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4
      let (regs, finalMem) ← evalWalkAccount1OwnerHiAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 0xC3 && regs .br2 == 0xD4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xC3))) =
      some true := by
  native_decide

/-- Walked account-1 high owner limbs after skip agree with absolute `r6`-relative loads. -/
theorem walkAccount1OwnerHiAfterSkip_eq_absLoad :
    (do
      let mem ← account1OwnerHiInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2 0xC3 0xD4
      let (regs, _) ← evalWalkAccount1OwnerHiAfterSkipToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount1OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0xC3 && owner3 == 0xD4)) =
      some true := by
  native_decide

/-!
## E-infinity knife 15 - Loader account-1 executable + rent_epoch after skip (`svm-sem-020`)

Knife 14 completes account-1 owner pubkey after the zero-`EXACT_DATA_LEN` skip. Emit then reads
account-1 executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout).
This knife composes that skip with those loads and proves agreement with absolute `r6`-relative
loads. Still not account-2 walk, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-1 executable and zero-dataLen rent_epoch. -/
def account1ExecutableOffset : Nat := account1HeaderOffset + 3
def account1RentEpochOffset : Nat :=
  account1HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account1ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1ExecutableOffset
def account1RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account1RentEpochOffset

/-- Seed skip+account-1 owner layout plus executable flag and rent_epoch. -/
def account1ExecRentInputMem (value arg0 key0Limb : U64) (nextMarker : U8)
    (rentEpoch key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1Rent : U64) : Option Mem := do
  let m₁ ← account1OwnerHiInputMem value arg0 key0Limb nextMarker rentEpoch key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3
  let m₂ ← storev .m8 m₁ account1ExecutableAddr (.vbyte executable)
  storev .m64 m₂ account1RentEpochAddr (.vlong acc1Rent)

/-- Typed skip then account-1 exec/rent: after knife-9 skip, `r2` is the account-1 header;
`ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`; stage executable. -/
def walkAccount1ExecRentAfterSkip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run skip+account-1 exec/rent walk against seeded input memory. -/
def evalWalkAccount1ExecRentAfterSkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1ExecRentAfterSkip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-1 executable and rent_epoch. -/
def evalAbsAccount1ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account1ExecutableAddr
  let rentEpoch ← loadv .m64 memory account1RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-1-exec-rent-after-skip assembly is well-formed. -/
theorem walkAccount1ExecRentAfterSkip_verified :
    (walkAccount1ExecRentAfterSkip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete skip+exec/rent: executable=`1`, rent_epoch=`0xEE`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount1_after_skip_executable_1_rent_0xEE :
    (do
      let mem ← account1ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE
      let (regs, finalMem) ← evalWalkAccount1ExecRentAfterSkipToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-1 exec/rent after skip agree with absolute `r6`-relative loads. -/
theorem walkAccount1ExecRentAfterSkip_eq_absLoad :
    (do
      let mem ← account1ExecRentInputMem 7 5 0x42 0xAB 0xEE 0x71 1 0 1000 128 0xA1 0xB2 0xC3 0xD4 0 0xEE
      let (regs, _) ← evalWalkAccount1ExecRentAfterSkipToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount1ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) =
      some true := by
  native_decide

/-!
## E-infinity knife 16 - Loader account-1 → account-2 marker skip chain (`svm-sem-021`)

Knife 15 completes account-1 fields after the account-0 skip. Emit chains the same
`emitSkipAccount` geometry from the account-1 header cursor to reach the next dup marker.
This knife composes the account-0 skip with an account-1 zero-dataLen skip and proves the
loaded account-2 marker matches an absolute `r6`-relative load. Still not account-2 meta
fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-2 dup marker after account-1 zero-dataLen rent. -/
def account2HeaderOffset : Nat := account1RentEpochOffset + 8
def account2HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2HeaderOffset

/-- Seed account-0/1 layout plus account-1 zero data_len and account-2 dup marker. -/
def account1SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) : Option Mem := do
  let m₁ ← account1ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
  let m₂ ← storev .m64 m₁ account1DataLenAddr (.vlong 0)
  storev .m8 m₂ account2HeaderAddr (.vbyte acc2Marker)

/-- Typed double skip: account-0 zero-dataLen skip lands on account-1 header, then the same
skip geometry from account-1 header reaches account-2 marker; stage marker. -/
def walkAccount1SkipNextAfterAccount0Skip? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1 skip-to-account-2-marker walk against seeded input memory. -/
def evalWalkAccount1SkipNextAfterAccount0SkipToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount1SkipNextAfterAccount0Skip? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-2 dup marker. -/
def evalAbsAccount2Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account2HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-1→account-2 skip-chain assembly is well-formed. -/
theorem walkAccount1SkipNextAfterAccount0Skip_verified :
    (walkAccount1SkipNextAfterAccount0Skip? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-2 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount1_skip_next_marker_0xff :
    (do
      let mem ← account1SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount1SkipNextAfterAccount0SkipToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-2 header. -/
theorem walkAccount1SkipNextAfterAccount0Skip_eq_absLoad :
    (do
      let mem ← account1SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAB
      let (regs, _) ← evalWalkAccount1SkipNextAfterAccount0SkipToStack? rhsStackOffset mem
      let marker ← evalAbsAccount2Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) =
      some true := by
  native_decide

/-!
## E-infinity knife 17 - Loader account-2 header/key after skip chain (`svm-sem-022`)

Knife 16 proves the chained skip lands on the account-2 dup marker. Emit then treats that
address as the account-2 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1 skip chain with an account-2 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-2 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-2 first key limb. -/
def account2KeyOffset : Nat := account2HeaderOffset + 8
def account2KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2KeyOffset

/-- Seed chained skip layout plus account-2 first key limb. -/
def account2MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) : Option Mem := do
  let m ← account1SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker
  storev .m64 m account2KeyAddr (.vlong key2Word)

/-- Typed double skip then account-2 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/
def walkAccount2MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run chained skip+account-2 meta walk against seeded input memory. -/
def evalWalkAccount2MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 dup marker and first key limb. -/
def evalAbsAccount2Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account2HeaderAddr
  let key ← loadv .m64 memory account2KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-2-meta-after-skip-chain assembly is well-formed. -/
theorem walkAccount2MetaAfterSkipChain_verified :
    (walkAccount2MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+meta: marker=`0xff`, key=`0x72`, key staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_key_0x72 :
    (do
      let mem ← account2MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72
      let (regs, finalMem) ← evalWalkAccount2MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x72 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x72))) =
      some true := by
  native_decide

/-- Walked account-2 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount2MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72
      let (regs, _) ← evalWalkAccount2MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount2Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAC && key == 0x72)) =
      some true := by
  native_decide

/-!
## E-infinity knife 18 - Loader account-2 signer/writable after skip chain (`svm-sem-023`)

Knife 17 lands the cursor on account-2 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the account-0/1 skip chain with those flag loads and
proves agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for
account-2, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-2 signer and writable flag bytes. -/
def account2SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account2HeaderOffset + 1)
def account2WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account2HeaderOffset + 2)

/-- Seed chained skip+account-2 meta layout plus signer/writable flags. -/
def account2FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8) : Option Mem := do
  let m₁ ← account2MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word
  let m₂ ← storev .m8 m₁ account2SignerAddr (.vbyte acc2Signer)
  storev .m8 m₂ account2WritableAddr (.vbyte acc2Writable)

/-- Typed double skip then account-2 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount2FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained skip+account-2 flag walk against seeded input memory. -/
def evalWalkAccount2FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 signer and writable flag bytes. -/
def evalAbsAccount2Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account2SignerAddr
  let writable ← loadv .m8 memory account2WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-2-flags-after-skip-chain assembly is well-formed. -/
theorem walkAccount2FlagsAfterSkipChain_verified :
    (walkAccount2FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_signer_writable_1 :
    (do
      let mem ← account2FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1
      let (regs, finalMem) ← evalWalkAccount2FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-2 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount2FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0
      let (regs, _) ← evalWalkAccount2FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount2Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 19 - Loader account-2 lamports/data_len after skip chain (`svm-sem-024`)

Knife 18 covers account-2 signer/writable after the skip chain. Emit then reads account-2
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes that skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not owner/executable/rent for account-2, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-2 lamports and data_len. -/
def account2LamportsOffset : Nat :=
  account2HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account2DataLenOffset : Nat :=
  account2HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account2LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2LamportsOffset
def account2DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2DataLenOffset

/-- Seed chained skip+account-2 flags layout plus lamports and data_len words. -/
def account2BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen : U64) : Option Mem := do
  let m₁ ← account2FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable
  let m₂ ← storev .m64 m₁ account2LamportsAddr (.vlong acc2Lamports)
  storev .m64 m₂ account2DataLenAddr (.vlong acc2DataLen)

/-- Typed double skip then account-2 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/
def walkAccount2BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained skip+account-2 budget walk against seeded input memory. -/
def evalWalkAccount2BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 lamports and data_len. -/
def evalAbsAccount2Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account2LamportsAddr
  let dataLen ← loadv .m64 memory account2DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-2-budget-after-skip-chain assembly is well-formed. -/
theorem walkAccount2BudgetAfterSkipChain_verified :
    (walkAccount2BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+budget: lamports=`2000`, data_len=`64`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_lamports_2000_dataLen_64 :
    (do
      let mem ← account2BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
      let (regs, finalMem) ← evalWalkAccount2BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 2000 && regs .br2 == 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 2000))) =
      some true := by
  native_decide

/-- Walked account-2 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount2BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64
      let (regs, _) ← evalWalkAccount2BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount2Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 2000 && dataLen == 64)) =
      some true := by
  native_decide

/-!
## E-infinity knife 20 - Loader account-2 owner limbs 0/1 after skip chain (`svm-sem-025`)

Knife 19 covers account-2 lamports/data_len after the skip chain. Emit then reads account-2
owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`). This knife composes
that skip chain with those word loads and proves agreement with absolute `r6`-relative loads.
Still not owner limbs 2/3, executable/rent for account-2, full vectors, syscalls, CPI, or ELF
accept.
-/

/-- Absolute offsets/VAs for account-2 owner limbs 0 and 1. -/
def account2Owner0Offset : Nat :=
  account2HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account2Owner1Offset : Nat :=
  account2HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account2Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2Owner0Offset
def account2Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2Owner1Offset

/-- Seed chained skip+account-2 budget layout plus owner limbs 0 and 1. -/
def account2OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 : U64) : Option Mem := do
  let m₁ ← account2BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen
  let m₂ ← storev .m64 m₁ account2Owner0Addr (.vlong acc2Owner0)
  storev .m64 m₂ account2Owner1Addr (.vlong acc2Owner1)

/-- Typed double skip then account-2 owner: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/
def walkAccount2OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained skip+account-2 owner walk against seeded input memory. -/
def evalWalkAccount2OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 owner limbs 0 and 1. -/
def evalAbsAccount2Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account2Owner0Addr
  let owner1 ← loadv .m64 memory account2Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-2-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount2OwnerAfterSkipChain_verified :
    (walkAccount2OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+owner: owner0=`0xE5`, owner1=`0xF6`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_owner0_0xE5_owner1_0xF6 :
    (do
      let mem ← account2OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6
      let (regs, finalMem) ← evalWalkAccount2OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE5 && regs .br2 == 0xF6 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE5))) =
      some true := by
  native_decide

/-- Walked account-2 owner limbs after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount2OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6
      let (regs, _) ← evalWalkAccount2OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount2Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE5 && owner1 == 0xF6)) =
      some true := by
  native_decide

/-!
## E-infinity knife 21 - Loader account-2 owner limbs 2/3 after skip chain (`svm-sem-026`)

Knife 20 covers account-2 owner limbs 0/1 after the skip chain. Emit then reads account-2 owner
limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`). This knife composes that skip
chain with those word loads and proves agreement with absolute `r6`-relative loads. Still not
executable/rent for account-2, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-2 owner limbs 2 and 3. -/
def account2Owner2Offset : Nat :=
  account2HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account2Owner3Offset : Nat :=
  account2HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account2Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2Owner2Offset
def account2Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2Owner3Offset

/-- Seed chained skip+account-2 owner layout plus owner limbs 2 and 3. -/
def account2OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64) :
    Option Mem := do
  let m₁ ← account2OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
  let m₂ ← storev .m64 m₁ account2Owner2Addr (.vlong acc2Owner2)
  storev .m64 m₂ account2Owner3Addr (.vlong acc2Owner3)

/-- Typed double skip then account-2 high owner: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/
def walkAccount2OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained skip+account-2 high-owner walk against seeded input memory. -/
def evalWalkAccount2OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 owner limbs 2 and 3. -/
def evalAbsAccount2OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account2Owner2Addr
  let owner3 ← loadv .m64 memory account2Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-2-high-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount2OwnerHiAfterSkipChain_verified :
    (walkAccount2OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+high-owner: owner2=`0x17`, owner3=`0x28`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_owner2_0x17_owner3_0x28 :
    (do
      let mem ← account2OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28
      let (regs, finalMem) ← evalWalkAccount2OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x17 && regs .br2 == 0x28 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x17))) =
      some true := by
  native_decide

/-- Walked account-2 high owner limbs after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount2OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28
      let (regs, _) ← evalWalkAccount2OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount2OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x17 && owner3 == 0x28)) =
      some true := by
  native_decide

/-!
## E-infinity knife 22 - Loader account-2 executable + rent_epoch after skip chain (`svm-sem-027`)

Knife 21 completes account-2 owner pubkey after the skip chain. Emit then reads account-2
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the account-0/1 skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-2 executable and zero-dataLen rent_epoch. -/
def account2ExecutableOffset : Nat := account2HeaderOffset + 3
def account2RentEpochOffset : Nat :=
  account2HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account2ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2ExecutableOffset
def account2RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account2RentEpochOffset

/-- Seed chained skip+account-2 owner layout plus executable flag and rent_epoch. -/
def account2ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) : Option Mem := do
  let m₁ ← account2OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen
      acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3
  let m₂ ← storev .m8 m₁ account2ExecutableAddr (.vbyte acc2Executable)
  storev .m64 m₂ account2RentEpochAddr (.vlong acc2Rent)

/-- Typed double skip then account-2 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/
def walkAccount2ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained skip+account-2 exec/rent walk against seeded input memory. -/
def evalWalkAccount2ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-2 executable and rent_epoch. -/
def evalAbsAccount2ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account2ExecutableAddr
  let rentEpoch ← loadv .m64 memory account2RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-2-exec-rent-after-skip-chain assembly is well-formed. -/
theorem walkAccount2ExecRentAfterSkipChain_verified :
    (walkAccount2ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip+exec/rent: executable=`1`, rent=`0xEE`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount2_after_skip_executable_1_rent_0xEE :
    (do
      let mem ← account2ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE
      let (regs, finalMem) ← evalWalkAccount2ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-2 exec/rent after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount2ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE
      let (regs, _) ← evalWalkAccount2ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount2ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) =
      some true := by
  native_decide

/-!
## E-infinity knife 23 - Loader account-2 → account-3 marker skip chain (`svm-sem-028`)

Knife 22 completes account-2 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-2 header cursor to reach the next dup marker.
This knife composes the account-0/1/2 skip chain with an account-2 zero-dataLen skip and
proves the loaded account-3 marker matches an absolute `r6`-relative load. Still not
account-3 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-3 dup marker after account-2 zero-dataLen rent. -/
def account3HeaderOffset : Nat := account2RentEpochOffset + 8
def account3HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3HeaderOffset

/-- Seed account-0/1/2 layout plus account-2 zero data_len and account-3 dup marker. -/
def account2SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) : Option Mem := do
  let m₁ ← account2ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent
  let m₂ ← storev .m64 m₁ account2DataLenAddr (.vlong 0)
  storev .m8 m₂ account3HeaderAddr (.vbyte acc3Marker)

/-- Typed triple skip: account-0/1/2 zero-dataLen skips land on account-3 marker; stage marker. -/
def walkAccount2SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2 skip-to-account-3-marker walk against seeded input memory. -/
def evalWalkAccount2SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount2SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-3 dup marker. -/
def evalAbsAccount3Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account3HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-2→account-3 skip-chain assembly is well-formed. -/
theorem walkAccount2SkipNextAfterSkipChain_verified :
    (walkAccount2SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-3 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount2_skip_next_marker_0xff :
    (do
      let mem ← account2SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount2SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-3 header. -/
theorem walkAccount2SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account2SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB
      let (regs, _) ← evalWalkAccount2SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount3Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAB)) =
      some true := by
  native_decide

/-!
## E-infinity knife 24 - Loader account-3 header/key after skip chain (`svm-sem-029`)

Knife 23 proves the triple skip lands on the account-3 dup marker. Emit then treats that
address as the account-3 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2 skip chain with an account-3 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-3 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-3 first key limb. -/
def account3KeyOffset : Nat := account3HeaderOffset + 8
def account3KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3KeyOffset

/-- Seed triple-skip layout plus account-3 first key limb. -/
def account3MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64) : Option Mem := do
  let m ← account2SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker
  storev .m64 m account3KeyAddr (.vlong key3Word)

/-- Typed triple skip then account-3 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/
def walkAccount3MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run triple skip+account-3 meta walk against seeded input memory. -/
def evalWalkAccount3MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 dup marker and first key limb. -/
def evalAbsAccount3Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account3HeaderAddr
  let key ← loadv .m64 memory account3KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-3-meta-after-skip-chain assembly is well-formed. -/
theorem walkAccount3MetaAfterSkipChain_verified :
    (walkAccount3MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+meta: marker=`0xff`, key=`0x73`, key staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_key_0x73 :
    (do
      let mem ← account3MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73
      let (regs, finalMem) ← evalWalkAccount3MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x73 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x73))) =
      some true := by
  native_decide

/-- Walked account-3 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount3MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73
      let (regs, _) ← evalWalkAccount3MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount3Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAB && key == 0x73)) =
      some true := by
  native_decide

/-!
## E-infinity knife 25 - Loader account-3 signer/writable after skip chain (`svm-sem-030`)

Knife 24 lands the cursor on account-3 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the account-0/1/2 skip chain with those flag loads and
proves agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for
account-3, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-3 signer and writable flag bytes. -/
def account3SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account3HeaderOffset + 1)
def account3WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account3HeaderOffset + 2)

/-- Seed triple-skip+account-3 meta layout plus signer/writable flags. -/
def account3FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) : Option Mem := do
  let m₁ ← account3MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word
  let m₂ ← storev .m8 m₁ account3SignerAddr (.vbyte acc3Signer)
  storev .m8 m₂ account3WritableAddr (.vbyte acc3Writable)

/-- Typed triple skip then account-3 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount3FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run triple skip+account-3 flag walk against seeded input memory. -/
def evalWalkAccount3FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 signer and writable flag bytes. -/
def evalAbsAccount3Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account3SignerAddr
  let writable ← loadv .m8 memory account3WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-3-flags-after-skip-chain assembly is well-formed. -/
theorem walkAccount3FlagsAfterSkipChain_verified :
    (walkAccount3FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_signer_writable_1 :
    (do
      let mem ← account3FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73 1 1
      let (regs, finalMem) ← evalWalkAccount3FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-3 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount3FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0
      let (regs, _) ← evalWalkAccount3FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount3Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 26 - Loader account-3 lamports/data_len after skip chain (`svm-sem-031`)

Knife 25 covers account-3 signer/writable after the skip chain. Emit then reads account-3
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes that skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not owner/executable/rent for account-3, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-3 lamports and data_len. -/
def account3LamportsOffset : Nat :=
  account3HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account3DataLenOffset : Nat :=
  account3HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account3LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3LamportsOffset
def account3DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3DataLenOffset

/-- Seed triple-skip+account-3 flags layout plus lamports and data_len words. -/
def account3BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen : U64) : Option Mem := do
  let m₁ ← account3FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
  let m₂ ← storev .m64 m₁ account3LamportsAddr (.vlong acc3Lamports)
  storev .m64 m₂ account3DataLenAddr (.vlong acc3DataLen)

/-- Typed triple skip then account-3 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/
def walkAccount3BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run triple skip+account-3 budget walk against seeded input memory. -/
def evalWalkAccount3BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 lamports and data_len. -/
def evalAbsAccount3Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account3LamportsAddr
  let dataLen ← loadv .m64 memory account3DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-3-budget-after-skip-chain assembly is well-formed. -/
theorem walkAccount3BudgetAfterSkipChain_verified :
    (walkAccount3BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+budget: lamports=`3000`, data_len=`96`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_lamports_3000_dataLen_96 :
    (do
      let mem ← account3BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64
          0xE5 0xF6 0x17 0x28 1 0xEE account0NonDupMarker 0x73 1 1 3000 96
      let (regs, finalMem) ← evalWalkAccount3BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 3000 && regs .br2 == 96 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 3000))) =
      some true := by
  native_decide

/-- Walked account-3 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount3BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96
      let (regs, _) ← evalWalkAccount3BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount3Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 3000 && dataLen == 96)) =
      some true := by
  native_decide

/-!
## E-infinity knife 27 - Loader account-3 owner limbs 0/1 after skip chain (`svm-sem-032`)

Knife 26 covers account-3 lamports/data_len after the skip chain. Emit then reads account-3
owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`). This knife composes
that skip chain with those word loads and proves agreement with absolute `r6`-relative loads.
Still not owner limbs 2/3, executable/rent for account-3, full vectors, syscalls, CPI, or ELF
accept.
-/

/-- Absolute offsets/VAs for account-3 owner limbs 0 and 1. -/
def account3Owner0Offset : Nat :=
  account3HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account3Owner1Offset : Nat :=
  account3HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account3Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3Owner0Offset
def account3Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3Owner1Offset

/-- Seed triple-skip+account-3 budget layout plus owner limbs 0 and 1. -/
def account3OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 : U64) :
    Option Mem := do
  let m₁ ← account3BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen
  let m₂ ← storev .m64 m₁ account3Owner0Addr (.vlong acc3Owner0)
  storev .m64 m₂ account3Owner1Addr (.vlong acc3Owner1)

/-- Typed triple skip then account-3 owner: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/
def walkAccount3OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run triple skip+account-3 owner walk against seeded input memory. -/
def evalWalkAccount3OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 owner limbs 0 and 1. -/
def evalAbsAccount3Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account3Owner0Addr
  let owner1 ← loadv .m64 memory account3Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-3-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount3OwnerAfterSkipChain_verified :
    (walkAccount3OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+owner: owner0=`0xE6`, owner1=`0xF7`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_owner0_0xE6_owner1_0xF7 :
    (do
      let mem ← account3OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7
      let (regs, finalMem) ← evalWalkAccount3OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE6 && regs .br2 == 0xF7 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE6))) =
      some true := by
  native_decide

/-- Walked account-3 owner limbs after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount3OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7
      let (regs, _) ← evalWalkAccount3OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount3Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE6 && owner1 == 0xF7)) =
      some true := by
  native_decide

/-!
## E-infinity knife 28 - Loader account-3 owner limbs 2/3 after skip chain (`svm-sem-033`)

Knife 27 covers account-3 owner limbs 0/1 after the skip chain. Emit then reads account-3
owner limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`). This knife composes
that skip chain with those word loads and proves agreement with absolute `r6`-relative loads.
Still not executable/rent for account-3, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-3 owner limbs 2 and 3. -/
def account3Owner2Offset : Nat :=
  account3HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account3Owner3Offset : Nat :=
  account3HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account3Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3Owner2Offset
def account3Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3Owner3Offset

/-- Seed triple-skip+account-3 owner layout plus owner limbs 2 and 3. -/
def account3OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) : Option Mem := do
  let m₁ ← account3OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
  let m₂ ← storev .m64 m₁ account3Owner2Addr (.vlong acc3Owner2)
  storev .m64 m₂ account3Owner3Addr (.vlong acc3Owner3)

/-- Typed triple skip then account-3 high owner: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/
def walkAccount3OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run triple skip+account-3 high-owner walk against seeded input memory. -/
def evalWalkAccount3OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 owner limbs 2 and 3. -/
def evalAbsAccount3OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account3Owner2Addr
  let owner3 ← loadv .m64 memory account3Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-3-high-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount3OwnerHiAfterSkipChain_verified :
    (walkAccount3OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+high-owner: owner2=`0x18`, owner3=`0x29`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_owner2_0x18_owner3_0x29 :
    (do
      let mem ← account3OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29
      let (regs, finalMem) ← evalWalkAccount3OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x18 && regs .br2 == 0x29 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x18))) =
      some true := by
  native_decide

/-- Walked account-3 high owner limbs after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount3OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29
      let (regs, _) ← evalWalkAccount3OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount3OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x18 && owner3 == 0x29)) =
      some true := by
  native_decide

/-!
## E-infinity knife 29 - Loader account-3 executable + rent_epoch after skip chain (`svm-sem-034`)

Knife 28 completes account-3 owner pubkey after the skip chain. Emit then reads account-3
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the account-0/1/2 skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-3 executable and zero-dataLen rent_epoch. -/
def account3ExecutableOffset : Nat := account3HeaderOffset + 3
def account3RentEpochOffset : Nat :=
  account3HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account3ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3ExecutableOffset
def account3RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account3RentEpochOffset

/-- Seed triple-skip+account-3 owner layout plus executable flag and rent_epoch. -/
def account3ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) : Option Mem := do
  let m₁ ← account3OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3
  let m₂ ← storev .m8 m₁ account3ExecutableAddr (.vbyte acc3Executable)
  storev .m64 m₂ account3RentEpochAddr (.vlong acc3Rent)

/-- Typed triple skip then account-3 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/
def walkAccount3ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run triple skip+account-3 exec/rent walk against seeded input memory. -/
def evalWalkAccount3ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-3 executable and rent_epoch. -/
def evalAbsAccount3ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account3ExecutableAddr
  let rentEpoch ← loadv .m64 memory account3RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-3-exec-rent-after-skip-chain assembly is well-formed. -/
theorem walkAccount3ExecRentAfterSkipChain_verified :
    (walkAccount3ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete triple skip+exec/rent: executable=`1`, rent=`0xEE`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount3_after_skip_executable_1_rent_0xEE :
    (do
      let mem ← account3ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE
      let (regs, finalMem) ← evalWalkAccount3ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-3 exec/rent after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount3ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE
      let (regs, _) ← evalWalkAccount3ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount3ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEE)) =
      some true := by
  native_decide

/-!
## E-infinity knife 30 - Loader account-3 → account-4 marker skip chain (`svm-sem-035`)

Knife 29 completes account-3 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-3 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3 skip chain with an account-3 zero-dataLen skip and
proves the loaded account-4 marker matches an absolute `r6`-relative load. Still not
account-4 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-4 dup marker after account-3 zero-dataLen rent. -/
def account4HeaderOffset : Nat := account3RentEpochOffset + 8
def account4HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4HeaderOffset

/-- Seed account-0/1/2/3 layout plus account-3 zero data_len and account-4 dup marker. -/
def account3SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8) :
    Option Mem := do
  let m₁ ← account3ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
  let m₂ ← storev .m64 m₁ account3DataLenAddr (.vlong 0)
  storev .m8 m₂ account4HeaderAddr (.vbyte acc4Marker)

/-- Typed quadruple skip: account-0/1/2/3 zero-dataLen skips land on account-4 marker. -/
def walkAccount3SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3 skip-to-account-4-marker walk against seeded input memory. -/
def evalWalkAccount3SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount3SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-4 dup marker. -/
def evalAbsAccount4Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account4HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-3→account-4 skip-chain assembly is well-formed. -/
theorem walkAccount3SkipNextAfterSkipChain_verified :
    (walkAccount3SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-4 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount3_skip_next_marker_0xff :
    (do
      let mem ← account3SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount3SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-4 header. -/
theorem walkAccount3SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account3SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAC
      let (regs, _) ← evalWalkAccount3SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount4Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAC)) =
      some true := by
  native_decide

/-!
## E-infinity knife 31 - Loader account-4 header/key after skip chain (`svm-sem-036`)

Knife 30 proves the quadruple skip lands on the account-4 dup marker. Emit then treats that
address as the account-4 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3 skip chain with an account-4 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-4 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-4 first key limb. -/
def account4KeyOffset : Nat := account4HeaderOffset + 8
def account4KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4KeyOffset

/-- Seed quadruple-skip layout plus account-4 first key limb. -/
def account4MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) : Option Mem := do
  let m ← account3SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker
  storev .m64 m account4KeyAddr (.vlong key4Word)

/-- Typed quadruple skip then account-4 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/
def walkAccount4MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run quadruple skip+account-4 meta walk against seeded input memory. -/
def evalWalkAccount4MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 dup marker and first key limb. -/
def evalAbsAccount4Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account4HeaderAddr
  let key ← loadv .m64 memory account4KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-4-meta-after-skip-chain assembly is well-formed. -/
theorem walkAccount4MetaAfterSkipChain_verified :
    (walkAccount4MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+meta: marker=`0xff`, key=`0x74`, key staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_key_0x74 :
    (do
      let mem ← account4MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74
      let (regs, finalMem) ← evalWalkAccount4MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x74 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x74))) =
      some true := by
  native_decide

/-- Walked account-4 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount4MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74
      let (regs, _) ← evalWalkAccount4MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount4Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAD && key == 0x74)) =
      some true := by
  native_decide

/-!
## E-infinity knife 32 - Loader account-4 signer/writable after skip chain (`svm-sem-037`)

Knife 31 lands the cursor on account-4 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the account-0/1/2/3 skip chain with those flag loads and
proves agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for
account-4, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-4 signer and writable flag bytes. -/
def account4SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account4HeaderOffset + 1)
def account4WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account4HeaderOffset + 2)

/-- Seed quadruple-skip+account-4 meta layout plus signer/writable flags. -/
def account4FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) : Option Mem := do
  let m₁ ← account4MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word
  let m₂ ← storev .m8 m₁ account4SignerAddr (.vbyte acc4Signer)
  storev .m8 m₂ account4WritableAddr (.vbyte acc4Writable)

/-- Typed quadruple skip then account-4 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount4FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quadruple skip+account-4 flag walk against seeded input memory. -/
def evalWalkAccount4FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 signer and writable flag bytes. -/
def evalAbsAccount4Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account4SignerAddr
  let writable ← loadv .m8 memory account4WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-4-flags-after-skip-chain assembly is well-formed. -/
theorem walkAccount4FlagsAfterSkipChain_verified :
    (walkAccount4FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_signer_writable_1 :
    (do
      let mem ← account4FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1
      let (regs, finalMem) ← evalWalkAccount4FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-4 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount4FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0
      let (regs, _) ← evalWalkAccount4FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount4Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 33 - Loader account-4 lamports/data_len after skip chain (`svm-sem-038`)

Knife 32 covers account-4 signer/writable after the skip chain. Emit then reads account-4
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes that skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not owner/executable/rent for account-4, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-4 lamports and data_len. -/
def account4LamportsOffset : Nat :=
  account4HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account4DataLenOffset : Nat :=
  account4HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account4LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4LamportsOffset
def account4DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4DataLenOffset

/-- Seed quadruple-skip+account-4 flags layout plus lamports and data_len words. -/
def account4BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen : U64) :
    Option Mem := do
  let m₁ ← account4FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable
  let m₂ ← storev .m64 m₁ account4LamportsAddr (.vlong acc4Lamports)
  storev .m64 m₂ account4DataLenAddr (.vlong acc4DataLen)

/-- Typed quadruple skip then account-4 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/
def walkAccount4BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quadruple skip+account-4 budget walk against seeded input memory. -/
def evalWalkAccount4BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 lamports and data_len. -/
def evalAbsAccount4Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account4LamportsAddr
  let dataLen ← loadv .m64 memory account4DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-4-budget-after-skip-chain assembly is well-formed. -/
theorem walkAccount4BudgetAfterSkipChain_verified :
    (walkAccount4BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+budget: lamports=`4000`, data_len=`112`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_lamports_4000_dataLen_112 :
    (do
      let mem ← account4BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112
      let (regs, finalMem) ← evalWalkAccount4BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 4000 && regs .br2 == 112 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 4000))) =
      some true := by
  native_decide

/-- Walked account-4 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount4BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112
      let (regs, _) ← evalWalkAccount4BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount4Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 4000 && dataLen == 112)) =
      some true := by
  native_decide

/-!
## E-infinity knife 34 - Loader account-4 owner limbs 0/1 after skip chain (`svm-sem-039`)

Knife 33 covers account-4 lamports/data_len after the skip chain. Emit then reads account-4
owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`). This knife composes
that skip chain with those word loads and proves agreement with absolute `r6`-relative loads.
Still not owner limbs 2/3, executable/rent for account-4, full vectors, syscalls, CPI, or ELF
accept.
-/

/-- Absolute offsets/VAs for account-4 owner limbs 0 and 1. -/
def account4Owner0Offset : Nat :=
  account4HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account4Owner1Offset : Nat :=
  account4HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account4Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4Owner0Offset
def account4Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4Owner1Offset

/-- Seed quadruple-skip+account-4 budget layout plus owner limbs 0 and 1. -/
def account4OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 : U64) : Option Mem := do
  let m₁ ← account4BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen
  let m₂ ← storev .m64 m₁ account4Owner0Addr (.vlong acc4Owner0)
  storev .m64 m₂ account4Owner1Addr (.vlong acc4Owner1)

/-- Typed quadruple skip then account-4 owner: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/
def walkAccount4OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quadruple skip+account-4 owner walk against seeded input memory. -/
def evalWalkAccount4OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 owner limbs 0 and 1. -/
def evalAbsAccount4Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account4Owner0Addr
  let owner1 ← loadv .m64 memory account4Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-4-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount4OwnerAfterSkipChain_verified :
    (walkAccount4OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+owner: owner0=`0xE7`, owner1=`0xF8`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_owner0_0xE7_owner1_0xF8 :
    (do
      let mem ← account4OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8
      let (regs, finalMem) ← evalWalkAccount4OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE7 && regs .br2 == 0xF8 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE7))) =
      some true := by
  native_decide

/-- Walked account-4 owner after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount4OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8
      let (regs, _) ← evalWalkAccount4OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount4Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE7 && owner1 == 0xF8)) =
      some true := by
  native_decide

/-!
## E-infinity knife 35 - Loader account-4 owner limbs 2/3 after skip chain (`svm-sem-040`)

Knife 34 covers account-4 owner limbs 0/1 after the skip chain. Emit then reads account-4
owner limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`). This knife composes
that skip chain with those word loads and proves agreement with absolute `r6`-relative loads.
Still not executable/rent for account-4, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-4 owner limbs 2 and 3. -/
def account4Owner2Offset : Nat :=
  account4HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account4Owner3Offset : Nat :=
  account4HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account4Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4Owner2Offset
def account4Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4Owner3Offset

/-- Seed quadruple-skip+account-4 owner layout plus owner limbs 2 and 3. -/
def account4OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) : Option Mem := do
  let m₁ ← account4OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
  let m₂ ← storev .m64 m₁ account4Owner2Addr (.vlong acc4Owner2)
  storev .m64 m₂ account4Owner3Addr (.vlong acc4Owner3)

/-- Typed quadruple skip then account-4 high owner: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/
def walkAccount4OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quadruple skip+account-4 high-owner walk against seeded input memory. -/
def evalWalkAccount4OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 owner limbs 2 and 3. -/
def evalAbsAccount4OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account4Owner2Addr
  let owner3 ← loadv .m64 memory account4Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-4-high-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount4OwnerHiAfterSkipChain_verified :
    (walkAccount4OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+high-owner: owner2=`0x19`, owner3=`0x2A`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_owner2_0x19_owner3_0x2A :
    (do
      let mem ← account4OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A
      let (regs, finalMem) ← evalWalkAccount4OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x19 && regs .br2 == 0x2A &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x19))) =
      some true := by
  native_decide

/-- Walked account-4 high owner limbs after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount4OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A
      let (regs, _) ← evalWalkAccount4OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount4OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x19 && owner3 == 0x2A)) =
      some true := by
  native_decide

/-!
## E-infinity knife 36 - Loader account-4 executable + rent_epoch after skip chain (`svm-sem-041`)

Knife 35 completes account-4 owner pubkey after the skip chain. Emit then reads account-4
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the account-0/1/2/3 skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-4 executable and zero-dataLen rent_epoch. -/
def account4ExecutableOffset : Nat := account4HeaderOffset + 3
def account4RentEpochOffset : Nat :=
  account4HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account4ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4ExecutableOffset
def account4RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account4RentEpochOffset

/-- Seed quadruple-skip+account-4 owner layout plus executable flag and rent_epoch. -/
def account4ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64) :
    Option Mem := do
  let m₁ ← account4OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3
  let m₂ ← storev .m8 m₁ account4ExecutableAddr (.vbyte acc4Executable)
  storev .m64 m₂ account4RentEpochAddr (.vlong acc4Rent)

/-- Typed quadruple skip then account-4 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/
def walkAccount4ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quadruple skip+account-4 exec/rent walk against seeded input memory. -/
def evalWalkAccount4ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-4 executable and rent_epoch. -/
def evalAbsAccount4ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account4ExecutableAddr
  let rentEpoch ← loadv .m64 memory account4RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-4-exec-rent-after-skip-chain assembly is well-formed. -/
theorem walkAccount4ExecRentAfterSkipChain_verified :
    (walkAccount4ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quadruple skip+exec/rent: executable=`1`, rent=`0xEF`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount4_after_skip_executable_1_rent_0xEF :
    (do
      let mem ← account4ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF
      let (regs, finalMem) ← evalWalkAccount4ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xEF &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-4 exec/rent after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount4ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF
      let (regs, _) ← evalWalkAccount4ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rentEpoch) ← evalAbsAccount4ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rentEpoch &&
        executable == 0 && rentEpoch == 0xEF)) =
      some true := by
  native_decide

/-!
## E-infinity knife 37 - Loader account-4 → account-5 marker skip chain (`svm-sem-042`)

Knife 36 completes account-4 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-4 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4 skip chain with an account-4 zero-dataLen skip and
proves the loaded account-5 marker matches an absolute `r6`-relative load. Still not
account-5 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-5 dup marker after account-4 zero-dataLen rent. -/
def account5HeaderOffset : Nat := account4RentEpochOffset + 8
def account5HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5HeaderOffset

/-- Seed account-0/1/2/3/4 layout plus account-4 zero data_len and account-5 dup marker. -/
def account4SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) : Option Mem := do
  let m₁ ← account4ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent
  let m₂ ← storev .m64 m₁ account4DataLenAddr (.vlong 0)
  storev .m8 m₂ account5HeaderAddr (.vbyte acc5Marker)

/-- Typed quintuple skip: account-0/1/2/3/4 zero-dataLen skips land on account-5 marker. -/
def walkAccount4SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4 skip-to-account-5-marker walk against seeded input memory. -/
def evalWalkAccount4SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount4SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-5 dup marker. -/
def evalAbsAccount5Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account5HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-4→account-5 skip-chain assembly is well-formed. -/
theorem walkAccount4SkipNextAfterSkipChain_verified :
    (walkAccount4SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-5 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount4_skip_next_marker_0xff :
    (do
      let mem ← account4SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount4SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-5 header. -/
theorem walkAccount4SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account4SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAE
      let (regs, _) ← evalWalkAccount4SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount5Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xAE)) =
      some true := by
  native_decide

/-!
## E-infinity knife 38 - Loader account-5 header/key after skip chain (`svm-sem-043`)

Knife 37 proves the quintuple skip lands on the account-5 dup marker. Emit then treats that
address as the account-5 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4 skip chain with an account-5 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-5 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-5 first key limb. -/
def account5KeyOffset : Nat := account5HeaderOffset + 8
def account5KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5KeyOffset

/-- Seed quintuple-skip layout plus account-5 first key limb. -/
def account5MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) : Option Mem := do
  let m ← account4SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker
  storev .m64 m account5KeyAddr (.vlong key5Word)

/-- Typed quintuple skip then account-5 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/
def walkAccount5MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run quintuple skip+account-5 meta walk against seeded input memory. -/
def evalWalkAccount5MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 dup marker and first key limb. -/
def evalAbsAccount5Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account5HeaderAddr
  let key ← loadv .m64 memory account5KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-5-meta-after-skip-chain assembly is well-formed. -/
theorem walkAccount5MetaAfterSkipChain_verified :
    (walkAccount5MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+meta: marker=`0xff`, key=`0x75`, key staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_key_0x75 :
    (do
      let mem ← account5MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75
      let (regs, finalMem) ← evalWalkAccount5MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x75 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x75))) =
      some true := by
  native_decide

/-- Walked account-5 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount5MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75
      let (regs, _) ← evalWalkAccount5MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount5Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xAF && key == 0x75)) =
      some true := by
  native_decide

/-!
## E-infinity knife 39 - Loader account-5 signer/writable after skip chain (`svm-sem-044`)

Knife 38 lands the cursor on account-5 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the account-0/1/2/3/4 skip chain with those flag loads
and proves agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for
account-5, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-5 signer and writable flag bytes. -/
def account5SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account5HeaderOffset + 1)
def account5WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account5HeaderOffset + 2)

/-- Seed quintuple-skip+account-5 meta layout plus signer/writable flags. -/
def account5FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8) : Option Mem := do
  let m₁ ← account5MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word
  let m₂ ← storev .m8 m₁ account5SignerAddr (.vbyte acc5Signer)
  storev .m8 m₂ account5WritableAddr (.vbyte acc5Writable)

/-- Typed quintuple skip then account-5 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount5FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quintuple skip+account-5 flag walk against seeded input memory. -/
def evalWalkAccount5FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 signer and writable flag bytes. -/
def evalAbsAccount5Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account5SignerAddr
  let writable ← loadv .m8 memory account5WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-5-flags-after-skip-chain assembly is well-formed. -/
theorem walkAccount5FlagsAfterSkipChain_verified :
    (walkAccount5FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_signer_writable_1 :
    (do
      let mem ← account5FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1
      let (regs, finalMem) ← evalWalkAccount5FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-5 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount5FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0
      let (regs, _) ← evalWalkAccount5FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount5Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 40 - Loader account-5 lamports/data_len after skip chain (`svm-sem-045`)

Knife 39 covers account-5 signer/writable after the skip chain. Emit then reads account-5
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes the quintuple skip chain with those word loads and proves agreement with absolute
`r6`-relative loads. Still not owner/executable/rent for account-5, full vectors, syscalls,
CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-5 lamports and data_len. -/
def account5LamportsOffset : Nat :=
  account5HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account5DataLenOffset : Nat :=
  account5HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account5LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5LamportsOffset
def account5DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5DataLenOffset

/-- Seed quintuple-skip+account-5 flags layout plus lamports and data_len words. -/
def account5BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen : U64) : Option Mem := do
  let m₁ ← account5FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
  let m₂ ← storev .m64 m₁ account5LamportsAddr (.vlong acc5Lamports)
  storev .m64 m₂ account5DataLenAddr (.vlong acc5DataLen)

/-- Typed quintuple skip then account-5 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/
def walkAccount5BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quintuple skip+account-5 budget walk against seeded input memory. -/
def evalWalkAccount5BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 lamports and data_len. -/
def evalAbsAccount5Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account5LamportsAddr
  let dataLen ← loadv .m64 memory account5DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-5-budget-after-skip-chain assembly is well-formed. -/
theorem walkAccount5BudgetAfterSkipChain_verified :
    (walkAccount5BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+budget: lamports=`5000`, data_len=`128`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_lamports_5000_dataLen_128 :
    (do
      let mem ← account5BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128
      let (regs, finalMem) ← evalWalkAccount5BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 5000 && regs .br2 == 128 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 5000))) =
      some true := by
  native_decide

/-- Walked account-5 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount5BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128
      let (regs, _) ← evalWalkAccount5BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount5Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 5000 && dataLen == 128)) =
      some true := by
  native_decide

/-!
## E-infinity knife 41 - Loader account-5 owner limbs 0/1 after skip chain (`svm-sem-046`)

Knife 40 covers account-5 lamports/data_len after the skip chain. Emit then reads account-5
owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`). This knife composes
the quintuple skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not owner limbs 2/3, executable/rent for account-5, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offsets/VAs for account-5 owner limbs 0 and 1. -/
def account5Owner0Offset : Nat :=
  account5HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account5Owner1Offset : Nat :=
  account5HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account5Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5Owner0Offset
def account5Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5Owner1Offset

/-- Seed quintuple-skip+account-5 budget layout plus owner limbs 0 and 1. -/
def account5OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 : U64) : Option Mem := do
  let m₁ ← account5BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen
  let m₂ ← storev .m64 m₁ account5Owner0Addr (.vlong acc5Owner0)
  storev .m64 m₂ account5Owner1Addr (.vlong acc5Owner1)

/-- Typed quintuple skip then account-5 owner: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/
def walkAccount5OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quintuple skip+account-5 owner walk against seeded input memory. -/
def evalWalkAccount5OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 owner limbs 0 and 1. -/
def evalAbsAccount5Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account5Owner0Addr
  let owner1 ← loadv .m64 memory account5Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-5-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount5OwnerAfterSkipChain_verified :
    (walkAccount5OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+owner: owner0=`0xE8`, owner1=`0xF9`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_owner0_0xE8_owner1_0xF9 :
    (do
      let mem ← account5OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9
      let (regs, finalMem) ← evalWalkAccount5OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE8 && regs .br2 == 0xF9 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE8))) =
      some true := by
  native_decide

/-- Walked account-5 owner after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount5OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9
      let (regs, _) ← evalWalkAccount5OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount5Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE8 && owner1 == 0xF9)) =
      some true := by
  native_decide

/-!
## E-infinity knife 42 - Loader account-5 owner limbs 2/3 after skip chain (`svm-sem-047`)

Knife 41 covers account-5 owner limbs 0/1 after the skip chain. Emit then reads account-5
owner limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`). This knife composes
the quintuple skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not executable/rent for account-5, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-5 owner limbs 2 and 3. -/
def account5Owner2Offset : Nat :=
  account5HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account5Owner3Offset : Nat :=
  account5HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account5Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5Owner2Offset
def account5Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5Owner3Offset

/-- Seed quintuple-skip+account-5 owner layout plus owner limbs 2 and 3. -/
def account5OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64) :
    Option Mem := do
  let m₁ ← account5OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1
  let m₂ ← storev .m64 m₁ account5Owner2Addr (.vlong acc5Owner2)
  storev .m64 m₂ account5Owner3Addr (.vlong acc5Owner3)

/-- Typed quintuple skip then account-5 high owner: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/
def walkAccount5OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quintuple skip+account-5 high-owner walk against seeded input memory. -/
def evalWalkAccount5OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 owner limbs 2 and 3. -/
def evalAbsAccount5OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account5Owner2Addr
  let owner3 ← loadv .m64 memory account5Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-5-owner-hi-after-skip-chain assembly is well-formed. -/
theorem walkAccount5OwnerHiAfterSkipChain_verified :
    (walkAccount5OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+owner hi: owner2=`0x1A`, owner3=`0x2B`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_owner2_0x1A_owner3_0x2B :
    (do
      let mem ← account5OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B
      let (regs, finalMem) ← evalWalkAccount5OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1A && regs .br2 == 0x2B &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1A))) =
      some true := by
  native_decide

/-- Walked account-5 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount5OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B
      let (regs, _) ← evalWalkAccount5OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount5OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1A && owner3 == 0x2B)) =
      some true := by
  native_decide

/-!
## E-infinity knife 43 - Loader account-5 executable + rent_epoch after skip chain (`svm-sem-048`)

Knife 42 completes account-5 owner pubkey after the skip chain. Emit then reads account-5
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the quintuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-5 executable and zero-dataLen rent_epoch. -/
def account5ExecutableOffset : Nat := account5HeaderOffset + 3
def account5RentEpochOffset : Nat :=
  account5HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account5ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5ExecutableOffset
def account5RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account5RentEpochOffset

/-- Seed quintuple-skip+account-5 owner layout plus executable flag and rent_epoch. -/
def account5ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) : Option Mem := do
  let m₁ ← account5OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3
  let m₂ ← storev .m8 m₁ account5ExecutableAddr (.vbyte acc5Executable)
  storev .m64 m₂ account5RentEpochAddr (.vlong acc5Rent)

/-- Typed quintuple skip then account-5 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/
def walkAccount5ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run quintuple skip+account-5 exec/rent walk against seeded input memory. -/
def evalWalkAccount5ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-5 executable and rent_epoch. -/
def evalAbsAccount5ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account5ExecutableAddr
  let rentEpoch ← loadv .m64 memory account5RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-5-exec-rent-after-skip-chain assembly is well-formed. -/
theorem walkAccount5ExecRentAfterSkipChain_verified :
    (walkAccount5ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete quintuple skip+exec/rent: executable=`1`, rent=`0xF0`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount5_after_skip_executable_1_rent_0xF0 :
    (do
      let mem ← account5ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0
      let (regs, finalMem) ← evalWalkAccount5ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF0 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-5 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount5ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0
      let (regs, _) ← evalWalkAccount5ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount5ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 44 - Loader account-5 → account-6 marker skip chain (`svm-sem-049`)

Knife 43 completes account-5 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-5 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5 skip chain with an account-5 zero-dataLen skip and
proves the loaded account-6 marker matches an absolute `r6`-relative load. Still not
account-6 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-6 dup marker after account-5 zero-dataLen rent. -/
def account6HeaderOffset : Nat := account5RentEpochOffset + 8
def account6HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6HeaderOffset

/-- Seed account-0/1/2/3/4/5 layout plus account-5 zero data_len and account-6 dup marker. -/
def account5SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) : Option Mem := do
  let m₁ ← account5ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
  let m₂ ← storev .m64 m₁ account5DataLenAddr (.vlong 0)
  storev .m8 m₂ account6HeaderAddr (.vbyte acc6Marker)

/-- Typed sextuple skip: account-0/1/2/3/4/5 zero-dataLen skips land on account-6 marker. -/
def walkAccount5SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5 skip-to-account-6-marker walk against seeded input memory. -/
def evalWalkAccount5SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount5SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-6 dup marker. -/
def evalAbsAccount6Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account6HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-5→account-6 skip-chain assembly is well-formed. -/
theorem walkAccount5SkipNextAfterSkipChain_verified :
    (walkAccount5SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-6 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount5_skip_next_marker_0xff :
    (do
      let mem ← account5SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount5SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-6 header. -/
theorem walkAccount5SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account5SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB0
      let (regs, _) ← evalWalkAccount5SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount6Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 45 - Loader account-6 header/key after skip chain (`svm-sem-050`)

Knife 44 proves the sextuple skip lands on the account-6 dup marker. Emit then treats that
address as the account-6 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5 skip chain with an account-6 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-6 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-6 first key limb. -/
def account6KeyOffset : Nat := account6HeaderOffset + 8
def account6KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6KeyOffset

/-- Seed sextuple-skip layout plus account-6 first key limb. -/
def account6MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64) : Option Mem := do
  let m ← account5SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker
  storev .m64 m account6KeyAddr (.vlong key6Word)

/-- Typed sextuple skip then account-6 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/
def walkAccount6MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run sextuple skip+account-6 meta walk against seeded input memory. -/
def evalWalkAccount6MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 dup marker and first key limb. -/
def evalAbsAccount6Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account6HeaderAddr
  let key ← loadv .m64 memory account6KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-6-meta-after-skip-chain assembly is well-formed. -/
theorem walkAccount6MetaAfterSkipChain_verified :
    (walkAccount6MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+meta: marker=`0xff`, key=`0x76`, key staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_key_0x76 :
    (do
      let mem ← account6MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76
      let (regs, finalMem) ← evalWalkAccount6MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x76 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x76))) =
      some true := by
  native_decide

/-- Walked account-6 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount6MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76
      let (regs, _) ← evalWalkAccount6MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount6Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB1 && key == 0x76)) =
      some true := by
  native_decide

/-!
## E-infinity knife 46 - Loader account-6 signer/writable after skip chain (`svm-sem-051`)

Knife 45 lands the cursor on account-6 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the sextuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-6,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-6 signer and writable flag bytes. -/
def account6SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account6HeaderOffset + 1)
def account6WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account6HeaderOffset + 2)

/-- Seed sextuple-skip+account-6 meta layout plus signer/writable flags. -/
def account6FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) : Option Mem := do
  let m₁ ← account6MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word
  let m₂ ← storev .m8 m₁ account6SignerAddr (.vbyte acc6Signer)
  storev .m8 m₂ account6WritableAddr (.vbyte acc6Writable)

/-- Typed sextuple skip then account-6 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/
def walkAccount6FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run sextuple skip+account-6 flag walk against seeded input memory. -/
def evalWalkAccount6FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 signer and writable flag bytes. -/
def evalAbsAccount6Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account6SignerAddr
  let writable ← loadv .m8 memory account6WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-6-flags-after-skip-chain assembly is well-formed. -/
theorem walkAccount6FlagsAfterSkipChain_verified :
    (walkAccount6FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_signer_writable_1 :
    (do
      let mem ← account6FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1
      let (regs, finalMem) ← evalWalkAccount6FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-6 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount6FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0
      let (regs, _) ← evalWalkAccount6FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount6Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 47 - Loader account-6 lamports/data_len after skip chain (`svm-sem-052`)

Knife 46 covers account-6 signer/writable after the skip chain. Emit then reads account-6
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes the sextuple skip chain with those word loads and proves agreement with absolute
`r6`-relative loads. Still not owner/executable/rent for account-6, full vectors, syscalls,
CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-6 lamports and data_len. -/
def account6LamportsOffset : Nat :=
  account6HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account6DataLenOffset : Nat :=
  account6HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account6LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6LamportsOffset
def account6DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6DataLenOffset

/-- Seed sextuple-skip+account-6 flags layout plus lamports and data_len words. -/
def account6BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen : U64) : Option Mem := do
  let m₁ ← account6FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable
  let m₂ ← storev .m64 m₁ account6LamportsAddr (.vlong acc6Lamports)
  storev .m64 m₂ account6DataLenAddr (.vlong acc6DataLen)

/-- Typed sextuple skip then account-6 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/
def walkAccount6BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run sextuple skip+account-6 budget walk against seeded input memory. -/
def evalWalkAccount6BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 lamports and data_len. -/
def evalAbsAccount6Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account6LamportsAddr
  let dataLen ← loadv .m64 memory account6DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-6-budget-after-skip-chain assembly is well-formed. -/
theorem walkAccount6BudgetAfterSkipChain_verified :
    (walkAccount6BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+budget: lamports=`6000`, data_len=`144`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_lamports_6000_dataLen_144 :
    (do
      let mem ← account6BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144
      let (regs, finalMem) ← evalWalkAccount6BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 6000 && regs .br2 == 144 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 6000))) =
      some true := by
  native_decide

/-- Walked account-6 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount6BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144
      let (regs, _) ← evalWalkAccount6BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount6Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 6000 && dataLen == 144)) =
      some true := by
  native_decide

/-!
## E-infinity knife 48 - Loader account-6 owner limbs 0/1 after skip chain (`svm-sem-053`)

Knife 47 covers account-6 lamports/data_len after the skip chain. Emit then reads account-6
owner limbs 0/1 from the same advanced header cursor (`+0x28` / `+0x30`). This knife composes
the sextuple skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not owner limbs 2/3, executable/rent for account-6, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offsets/VAs for account-6 owner limbs 0 and 1. -/
def account6Owner0Offset : Nat :=
  account6HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account6Owner1Offset : Nat :=
  account6HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account6Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6Owner0Offset
def account6Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6Owner1Offset

/-- Seed sextuple-skip+account-6 budget layout plus owner limbs 0 and 1. -/
def account6OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1 : U64) :
    Option Mem := do
  let m₁ ← account6BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen
  let m₂ ← storev .m64 m₁ account6Owner0Addr (.vlong acc6Owner0)
  storev .m64 m₂ account6Owner1Addr (.vlong acc6Owner1)

/-- Typed sextuple skip then account-6 owner: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/
def walkAccount6OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run sextuple skip+account-6 owner walk against seeded input memory. -/
def evalWalkAccount6OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 owner limbs 0 and 1. -/
def evalAbsAccount6Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account6Owner0Addr
  let owner1 ← loadv .m64 memory account6Owner1Addr
  match owner0, owner1 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-6-owner-after-skip-chain assembly is well-formed. -/
theorem walkAccount6OwnerAfterSkipChain_verified :
    (walkAccount6OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+owner: owner0=`0xE9`, owner1=`0xFA`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_owner0_0xE9_owner1_0xFA :
    (do
      let mem ← account6OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA
      let (regs, finalMem) ← evalWalkAccount6OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xE9 && regs .br2 == 0xFA &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xE9))) =
      some true := by
  native_decide

/-- Walked account-6 owner after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount6OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA
      let (regs, _) ← evalWalkAccount6OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount6Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xE9 && owner1 == 0xFA)) =
      some true := by
  native_decide

/-!
## E-infinity knife 49 - Loader account-6 owner limbs 2/3 after skip chain (`svm-sem-054`)

Knife 48 covers account-6 owner limbs 0/1 after the skip chain. Emit then reads account-6
owner limbs 2/3 from the same advanced header cursor (`+0x38` / `+0x40`). This knife composes
the sextuple skip chain with those word loads and proves agreement with absolute `r6`-relative
loads. Still not executable/rent for account-6, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-6 owner limbs 2 and 3. -/
def account6Owner2Offset : Nat :=
  account6HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account6Owner3Offset : Nat :=
  account6HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account6Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6Owner2Offset
def account6Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6Owner3Offset

/-- Seed sextuple-skip+account-6 owner layout plus owner limbs 2 and 3. -/
def account6OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) : Option Mem := do
  let m₁ ← account6OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
  let m₂ ← storev .m64 m₁ account6Owner2Addr (.vlong acc6Owner2)
  storev .m64 m₂ account6Owner3Addr (.vlong acc6Owner3)

/-- Typed sextuple skip then account-6 high owner: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/
def walkAccount6OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run sextuple skip+account-6 high-owner walk against seeded input memory. -/
def evalWalkAccount6OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 owner limbs 2 and 3. -/
def evalAbsAccount6OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account6Owner2Addr
  let owner3 ← loadv .m64 memory account6Owner3Addr
  match owner2, owner3 with
  | .vlong a, .vlong b => some (a, b)
  | _, _ => none

/-- Walked account-6-owner-hi-after-skip-chain assembly is well-formed. -/
theorem walkAccount6OwnerHiAfterSkipChain_verified :
    (walkAccount6OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+owner hi: owner2=`0x1B`, owner3=`0x2C`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_owner2_0x1B_owner3_0x2C :
    (do
      let mem ← account6OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C
      let (regs, finalMem) ← evalWalkAccount6OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1B && regs .br2 == 0x2C &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1B))) =
      some true := by
  native_decide

/-- Walked account-6 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount6OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C
      let (regs, _) ← evalWalkAccount6OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount6OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1B && owner3 == 0x2C)) =
      some true := by
  native_decide

/-!
## E-infinity knife 50 - Loader account-6 executable + rent_epoch after skip chain (`svm-sem-055`)

Knife 49 completes account-6 owner pubkey after the skip chain. Emit then reads account-6
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the sextuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-6 executable and zero-dataLen rent_epoch. -/
def account6ExecutableOffset : Nat := account6HeaderOffset + 3
def account6RentEpochOffset : Nat :=
  account6HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account6ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6ExecutableOffset
def account6RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account6RentEpochOffset

/-- Seed sextuple-skip+account-6 owner layout plus executable flag and rent_epoch. -/
def account6ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64) : Option Mem := do
  let m₁ ← account6OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3
  let m₂ ← storev .m8 m₁ account6ExecutableAddr (.vbyte acc6Executable)
  storev .m64 m₂ account6RentEpochAddr (.vlong acc6Rent)

/-- Typed sextuple skip then account-6 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/
def walkAccount6ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run sextuple skip+account-6 exec/rent walk against seeded input memory. -/
def evalWalkAccount6ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-6 executable and rent_epoch. -/
def evalAbsAccount6ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account6ExecutableAddr
  let rentEpoch ← loadv .m64 memory account6RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-6-exec-rent-after-skip-chain assembly is well-formed. -/
theorem walkAccount6ExecRentAfterSkipChain_verified :
    (walkAccount6ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete sextuple skip+exec/rent: executable=`1`, rent=`0xF1`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount6_after_skip_executable_1_rent_0xF1 :
    (do
      let mem ← account6ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1
      let (regs, finalMem) ← evalWalkAccount6ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-6 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount6ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1
      let (regs, _) ← evalWalkAccount6ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount6ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF1)) =
      some true := by
  native_decide

/-!
## E-infinity knife 51 - Loader account-6 → account-7 marker skip chain (`svm-sem-056`)

Knife 50 completes account-6 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-6 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5/6 skip chain with an account-6 zero-dataLen skip
and proves the loaded account-7 marker matches an absolute `r6`-relative load. Still not
account-7 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-7 dup marker after account-6 zero-dataLen rent. -/
def account7HeaderOffset : Nat := account6RentEpochOffset + 8
def account7HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7HeaderOffset

/-- Seed account-0/1/2/3/4/5/6 layout plus account-6 zero data_len and account-7 dup marker. -/
def account6SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) : Option Mem := do
  let m₁ ← account6ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent
  let m₂ ← storev .m64 m₁ account6DataLenAddr (.vlong 0)
  storev .m8 m₂ account7HeaderAddr (.vbyte acc7Marker)

/-- Typed septuple skip: account-0/1/2/3/4/5/6 zero-dataLen skips land on account-7 marker. -/
def walkAccount6SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5/6 skip-to-account-7-marker walk against seeded input memory. -/
def evalWalkAccount6SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount6SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-7 dup marker. -/
def evalAbsAccount7Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account7HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-6→account-7 skip-chain assembly is well-formed. -/
theorem walkAccount6SkipNextAfterSkipChain_verified :
    (walkAccount6SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-7 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount6_skip_next_marker_0xff :
    (do
      let mem ← account6SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount6SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-7 header. -/
theorem walkAccount6SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account6SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2
      let (regs, _) ← evalWalkAccount6SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount7Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB2)) =
      some true := by
  native_decide


/-!
## E-infinity knife 52 - Loader account-7 header/key after skip chain (`svm-sem-057`)

Knife 51 proves the septuple skip lands on the account-7 dup marker. Emit then treats that
address as the account-7 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6 skip chain with an account-7 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-7 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-7 first key limb. -/
def account7KeyOffset : Nat := account7HeaderOffset + 8
def account7KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7KeyOffset

/-- Seed septuple-skip layout plus account-7 first key limb. -/
def account7MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) : Option Mem := do
  let m ← account6SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker
  storev .m64 m account7KeyAddr (.vlong key7Word)

/-- Typed septuple skip then account-7 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount7MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 dup marker and first key limb. -/
def evalAbsAccount7Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account7HeaderAddr
  let key ← loadv .m64 memory account7KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7MetaAfterSkipChain_verified :
    (walkAccount7MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+meta: marker=`0xff`, key=`0x77`, key staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_key_0x77 :
    (do
      let mem ← account7MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77
      let (regs, finalMem) ← evalWalkAccount7MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x77 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x77))) =
      some true := by
  native_decide

/-- Walked account-7 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount7MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77
      let (regs, _) ← evalWalkAccount7MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount7Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB3 && key == 0x77)) =
      some true := by
  native_decide


/-!
## E-infinity knife 53 - Loader account-7 signer/writable after skip chain (`svm-sem-058`)

Knife 52 lands the cursor on account-7 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the septuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-7,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-7 signer and writable flag bytes. -/
def account7SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account7HeaderOffset + 1)
def account7WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account7HeaderOffset + 2)

/-- Seed septuple-skip+account-7 meta layout plus signer/writable flags. -/
def account7FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8) : Option Mem := do
  let m₁ ← account7MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word
  let m₂ ← storev .m8 m₁ account7SignerAddr (.vbyte acc7Signer)
  storev .m8 m₂ account7WritableAddr (.vbyte acc7Writable)

/-- Typed septuple skip then account-7 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount7FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
        .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 signer and writable flag bytes. -/
def evalAbsAccount7Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account7SignerAddr
  let writable ← loadv .m8 memory account7WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7FlagsAfterSkipChain_verified :
    (walkAccount7FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_signer_writable_1 :
    (do
      let mem ← account7FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1
      let (regs, finalMem) ← evalWalkAccount7FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-7 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount7FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0
      let (regs, _) ← evalWalkAccount7FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount7Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide


/-!
## E-infinity knife 54 - Loader account-7 lamports/data_len after skip chain (`svm-sem-059`)

Knife 53 covers account-7 signer/writable after the skip chain. Emit then reads account-7
lamports and data_len from the same advanced header cursor (`+0x48` / `+0x50`). This knife
composes the septuple skip chain with those word loads and proves agreement with absolute
`r6`-relative loads. Still not owner/executable/rent for account-7, full vectors, syscalls,
CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-7 lamports and data_len. -/
def account7LamportsOffset : Nat :=
  account7HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account7DataLenOffset : Nat :=
  account7HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account7LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7LamportsOffset
def account7DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7DataLenOffset

/-- Seed septuple-skip+account-7 flags layout plus lamports and data_len words. -/
def account7BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen : U64) : Option Mem := do
  let m₁ ← account7FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
  let m₂ ← storev .m64 m₁ account7LamportsAddr (.vlong acc7Lamports)
  storev .m64 m₂ account7DataLenAddr (.vlong acc7DataLen)

/-- Typed septuple skip then account-7 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount7BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let accDataLenOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
        .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 accDataLenOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 lamports and data_len. -/
def evalAbsAccount7Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account7LamportsAddr
  let dataLen ← loadv .m64 memory account7DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7BudgetAfterSkipChain_verified :
    (walkAccount7BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+budget: lamports=`7000`, data_len=`160`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_lamports_7000_dataLen_160 :
    (do
      let mem ← account7BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160
      let (regs, finalMem) ← evalWalkAccount7BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 7000 && regs .br2 == 160 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 7000))) =
      some true := by
  native_decide

/-- Walked account-7 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount7BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160
      let (regs, _) ← evalWalkAccount7BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount7Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 7000 && dataLen == 160)) =
      some true := by
  native_decide


/-!
## E-infinity knife 55 - Loader account-7 owner limbs 0/1 after skip chain (`svm-sem-060`)

Knife 54 completes account-7 lamports/data_len after the skip chain. Emit then reads account-7
owner pubkey limbs 0 and 1 (`+0x28` / `+0x30`). This knife composes the septuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not owner
limbs 2/3 or exec/rent for account-7, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-7 owner limbs 0 and 1. -/
def account7Owner0Offset : Nat :=
  account7HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account7Owner1Offset : Nat :=
  account7HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account7Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7Owner0Offset
def account7Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7Owner1Offset

/-- Seed septuple-skip+account-7 budget layout plus owner limbs 0/1. -/
def account7OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 : U64) : Option Mem := do
  let m₁ ← account7BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen
  let m₂ ← storev .m64 m₁ account7Owner0Addr (.vlong acc7Owner0)
  storev .m64 m₂ account7Owner1Addr (.vlong acc7Owner1)

/-- Typed septuple skip then account-7 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount7OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
        .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 owner limbs 0 and 1. -/
def evalAbsAccount7Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account7Owner0Addr
  let owner1 ← loadv .m64 memory account7Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7OwnerAfterSkipChain_verified :
    (walkAccount7OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+owner lo: owner0=`0xEA`, owner1=`0xFB`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_owner0_0xEA_owner1_0xFB :
    (do
      let mem ← account7OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB
      let (regs, finalMem) ← evalWalkAccount7OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xEA && regs .br2 == 0xFB &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xEA))) =
      some true := by
  native_decide

/-- Walked account-7 owner lo after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount7OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB
      let (regs, _) ← evalWalkAccount7OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount7Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xEA && owner1 == 0xFB)) =
      some true := by
  native_decide


/-!
## E-infinity knife 56 - Loader account-7 owner limbs 2/3 after skip chain (`svm-sem-061`)

Knife 55 completes account-7 owner limbs 0/1 after the skip chain. Emit then reads account-7
owner pubkey limbs 2 and 3 (`+0x38` / `+0x40`). This knife composes the septuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not
exec/rent for account-7, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-7 owner limbs 2 and 3. -/
def account7Owner2Offset : Nat :=
  account7HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account7Owner3Offset : Nat :=
  account7HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account7Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7Owner2Offset
def account7Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7Owner3Offset

/-- Seed septuple-skip+account-7 owner lo layout plus owner limbs 2/3. -/
def account7OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64) : Option Mem := do
  let m₁ ← account7OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1
  let m₂ ← storev .m64 m₁ account7Owner2Addr (.vlong acc7Owner2)
  storev .m64 m₂ account7Owner3Addr (.vlong acc7Owner3)

/-- Typed septuple skip then account-7 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount7OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
        .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 owner limbs 2 and 3. -/
def evalAbsAccount7OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account7Owner2Addr
  let owner3 ← loadv .m64 memory account7Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7OwnerHiAfterSkipChain_verified :
    (walkAccount7OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+owner hi: owner2=`0x1C`, owner3=`0x2D`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_owner2_0x1C_owner3_0x2D :
    (do
      let mem ← account7OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D
      let (regs, finalMem) ← evalWalkAccount7OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1C && regs .br2 == 0x2D &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1C))) =
      some true := by
  native_decide

/-- Walked account-7 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount7OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D
      let (regs, _) ← evalWalkAccount7OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount7OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1C && owner3 == 0x2D)) =
      some true := by
  native_decide


/-!
## E-infinity knife 57 - Loader account-7 executable + rent_epoch after skip chain (`svm-sem-062`)

Knife 56 completes account-7 owner pubkey after the skip chain. Emit then reads account-7
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the septuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-7 executable and zero-dataLen rent_epoch. -/
def account7ExecutableOffset : Nat := account7HeaderOffset + 3
def account7RentEpochOffset : Nat :=
  account7HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account7ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7ExecutableOffset
def account7RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account7RentEpochOffset

/-- Seed septuple-skip+account-7 owner layout plus executable flag and rent_epoch. -/
def account7ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) : Option Mem := do
  let m₁ ← account7OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3
  let m₂ ← storev .m8 m₁ account7ExecutableAddr (.vbyte acc7Executable)
  storev .m64 m₂ account7RentEpochAddr (.vlong acc7Rent)

/-- Typed septuple skip then account-7 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount7ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
        .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run septuple skip+account-7 walk against seeded input memory. -/
def evalWalkAccount7ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-7 executable and rent_epoch. -/
def evalAbsAccount7ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account7ExecutableAddr
  let rentEpoch ← loadv .m64 memory account7RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-7 assembly after skip chain is well-formed. -/
theorem walkAccount7ExecRentAfterSkipChain_verified :
    (walkAccount7ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete septuple skip+exec/rent: executable=`1`, rent=`0xF2`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount7_after_skip_executable_1_rent_0xF2 :
    (do
      let mem ← account7ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2
      let (regs, finalMem) ← evalWalkAccount7ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF2 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-7 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount7ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2
      let (regs, _) ← evalWalkAccount7ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount7ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF2)) =
      some true := by
  native_decide

/-!
## E-infinity knife 58 - Loader account-7 → account-8 marker skip chain (`svm-sem-063`)

Knife 57 completes account-7 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-7 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5/6/7 skip chain with an account-7 zero-dataLen skip
and proves the loaded account-8 marker matches an absolute `r6`-relative load. Still not
account-8 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-8 dup marker after account-7 zero-dataLen rent. -/
def account8HeaderOffset : Nat := account7RentEpochOffset + 8
def account8HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8HeaderOffset

/-- Seed account-0/1/2/3/4/5/6/7 layout plus account-7 zero data_len and account-8 dup marker. -/
def account7SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) : Option Mem := do
  let m₁ ← account7ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
  let m₂ ← storev .m64 m₁ account7DataLenAddr (.vlong 0)
  storev .m8 m₂ account8HeaderAddr (.vbyte acc8Marker)

/-- Typed octuple skip: account-0/1/2/3/4/5/6/7 zero-dataLen skips land on account-8 marker. -/
def walkAccount7SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5/6/7 skip-to-account-8-marker walk against seeded input memory. -/
def evalWalkAccount7SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount7SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-8 dup marker. -/
def evalAbsAccount8Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account8HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-7→account-8 skip-chain assembly is well-formed. -/
theorem walkAccount7SkipNextAfterSkipChain_verified :
    (walkAccount7SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-8 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount7_skip_next_marker_0xff :
    (do
      let mem ← account7SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount7SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-8 header. -/
theorem walkAccount7SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account7SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB3
      let (regs, _) ← evalWalkAccount7SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount8Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB3)) =
      some true := by
  native_decide

/-!
## E-infinity knife 59 - Loader account-8 header/key after skip chain (`svm-sem-064`)

Knife 58 proves the octuple skip lands on the account-8 dup marker. Emit then treats that
address as the account-8 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6/7 skip chain with an account-8 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-8 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-8 first key limb. -/
def account8KeyOffset : Nat := account8HeaderOffset + 8
def account8KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8KeyOffset

/-- Seed octuple-skip layout plus account-8 first key limb. -/
def account8MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64) : Option Mem := do
  let m ← account7SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
  storev .m64 m account8KeyAddr (.vlong key8Word)

/-- Typed octuple skip then account-8 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount8MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 dup marker and first key limb. -/
def evalAbsAccount8Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account8HeaderAddr
  let key ← loadv .m64 memory account8KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8MetaAfterSkipChain_verified :
    (walkAccount8MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+meta: marker=`0xff`, key=`0x78`, key staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_key_0x78 :
    (do
      let mem ← account8MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78
      let (regs, finalMem) ← evalWalkAccount8MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x78 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x78))) =
      some true := by
  native_decide

/-- Walked account-8 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount8MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78
      let (regs, _) ← evalWalkAccount8MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount8Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB4 && key == 0x78)) =
      some true := by
  native_decide

/-!
## E-infinity knife 60 - Loader account-8 signer/writable after skip chain (`svm-sem-065`)

Knife 59 lands the cursor on account-8 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the octuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-8,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-8 signer and writable flag bytes. -/
def account8SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account8HeaderOffset + 1)
def account8WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account8HeaderOffset + 2)

/-- Seed octuple-skip+account-8 meta layout plus signer/writable flags. -/
def account8FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64)
    (acc8Signer acc8Writable : U8) : Option Mem := do
  let m₁ ← account8MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
      key8Word
  let m₂ ← storev .m8 m₁ account8SignerAddr (.vbyte acc8Signer)
  storev .m8 m₂ account8WritableAddr (.vbyte acc8Writable)

/-- Typed octuple skip then account-8 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount8FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 signer and writable flag bytes. -/
def evalAbsAccount8Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account8SignerAddr
  let writable ← loadv .m8 memory account8WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8FlagsAfterSkipChain_verified :
    (walkAccount8FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_signer_writable_1 :
    (do
      let mem ← account8FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78 1 1
      let (regs, finalMem) ← evalWalkAccount8FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-8 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount8FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78 1 0
      let (regs, _) ← evalWalkAccount8FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount8Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 61 - Loader account-8 lamports/data_len after skip chain (`svm-sem-066`)

Knife 60 covers account-8 signer/writable after the skip chain. Emit then reads account-8
lamports and data_len (`+0x48` / `+0x50`). This knife composes the octuple skip chain with
those word loads and proves agreement with absolute `r6`-relative loads. Still not owner/executable/rent
for account-8, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-8 lamports and data_len. -/
def account8LamportsOffset : Nat :=
  account8HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account8DataLenOffset : Nat :=
  account8HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account8LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8LamportsOffset
def account8DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8DataLenOffset

/-- Seed octuple-skip+account-8 flags layout plus lamports and data_len words. -/
def account8BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64)
    (acc8Signer acc8Writable : U8)
    (acc8Lamports acc8DataLen : U64) : Option Mem := do
  let m₁ ← account8FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
      key8Word
      acc8Signer acc8Writable
  let m₂ ← storev .m64 m₁ account8LamportsAddr (.vlong acc8Lamports)
  storev .m64 m₂ account8DataLenAddr (.vlong acc8DataLen)

/-- Typed octuple skip then account-8 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount8BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenFieldOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 dataLenFieldOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 lamports and data_len. -/
def evalAbsAccount8Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account8LamportsAddr
  let dataLen ← loadv .m64 memory account8DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8BudgetAfterSkipChain_verified :
    (walkAccount8BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+budget: lamports=`8000`, data_len=`176`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_lamports_8000_dataLen_176 :
    (do
      let mem ← account8BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78 1 1 8000 176
      let (regs, finalMem) ← evalWalkAccount8BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 8000 && regs .br2 == 176 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 8000))) =
      some true := by
  native_decide

/-- Walked account-8 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount8BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78 1 0 8000 176
      let (regs, _) ← evalWalkAccount8BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount8Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 8000 && dataLen == 176)) =
      some true := by
  native_decide

/-!
## E-infinity knife 62 - Loader account-8 owner limbs 0/1 after skip chain (`svm-sem-067`)

Knife 61 completes account-8 lamports/data_len after the skip chain. Emit then reads account-8
owner pubkey limbs 0 and 1 (`+0x28` / `+0x30`). This knife composes the octuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not owner
limbs 2/3 or exec/rent for account-8, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-8 owner limbs 0 and 1. -/
def account8Owner0Offset : Nat :=
  account8HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account8Owner1Offset : Nat :=
  account8HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account8Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8Owner0Offset
def account8Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8Owner1Offset

/-- Seed octuple-skip+account-8 budget layout plus owner limbs 0/1. -/
def account8OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64)
    (acc8Signer acc8Writable : U8)
    (acc8Lamports acc8DataLen : U64)
    (acc8Owner0 acc8Owner1 : U64) : Option Mem := do
  let m₁ ← account8BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
      key8Word
      acc8Signer acc8Writable
      acc8Lamports acc8DataLen
  let m₂ ← storev .m64 m₁ account8Owner0Addr (.vlong acc8Owner0)
  storev .m64 m₂ account8Owner1Addr (.vlong acc8Owner1)

/-- Typed octuple skip then account-8 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount8OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 owner limbs 0 and 1. -/
def evalAbsAccount8Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account8Owner0Addr
  let owner1 ← loadv .m64 memory account8Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8OwnerAfterSkipChain_verified :
    (walkAccount8OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+owner lo: owner0=`0xEB`, owner1=`0xFC`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_owner0_0xEB_owner1_0xFC :
    (do
      let mem ← account8OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78 1 1 8000 176 0xEB 0xFC
      let (regs, finalMem) ← evalWalkAccount8OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xEB && regs .br2 == 0xFC &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xEB))) =
      some true := by
  native_decide

/-- Walked account-8 owner lo after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount8OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78 1 0 8000 176 0xEB 0xFC
      let (regs, _) ← evalWalkAccount8OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount8Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xEB && owner1 == 0xFC)) =
      some true := by
  native_decide

/-!
## E-infinity knife 63 - Loader account-8 owner limbs 2/3 after skip chain (`svm-sem-068`)

Knife 62 completes account-8 owner limbs 0/1 after the skip chain. Emit then reads account-8
owner pubkey limbs 2 and 3 (`+0x38` / `+0x40`). This knife composes the octuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not
exec/rent for account-8, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-8 owner limbs 2 and 3. -/
def account8Owner2Offset : Nat :=
  account8HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account8Owner3Offset : Nat :=
  account8HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account8Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8Owner2Offset
def account8Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8Owner3Offset

/-- Seed octuple-skip+account-8 owner lo layout plus owner limbs 2/3. -/
def account8OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64)
    (acc8Signer acc8Writable : U8)
    (acc8Lamports acc8DataLen : U64)
    (acc8Owner0 acc8Owner1 : U64)
    (acc8Owner2 acc8Owner3 : U64) : Option Mem := do
  let m₁ ← account8OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
      key8Word
      acc8Signer acc8Writable
      acc8Lamports acc8DataLen
      acc8Owner0 acc8Owner1
  let m₂ ← storev .m64 m₁ account8Owner2Addr (.vlong acc8Owner2)
  storev .m64 m₂ account8Owner3Addr (.vlong acc8Owner3)

/-- Typed octuple skip then account-8 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount8OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 owner limbs 2 and 3. -/
def evalAbsAccount8OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account8Owner2Addr
  let owner3 ← loadv .m64 memory account8Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8OwnerHiAfterSkipChain_verified :
    (walkAccount8OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+owner hi: owner2=`0x1D`, owner3=`0x2E`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_owner2_0x1D_owner3_0x2E :
    (do
      let mem ← account8OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E
      let (regs, finalMem) ← evalWalkAccount8OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1D && regs .br2 == 0x2E &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1D))) =
      some true := by
  native_decide

/-- Walked account-8 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount8OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E
      let (regs, _) ← evalWalkAccount8OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount8OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1D && owner3 == 0x2E)) =
      some true := by
  native_decide

/-!
## E-infinity knife 64 - Loader account-8 executable + rent_epoch after skip chain (`svm-sem-069`)

Knife 63 completes account-8 owner pubkey after the skip chain. Emit then reads account-8
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the octuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-8 executable and zero-dataLen rent_epoch. -/
def account8ExecutableOffset : Nat := account8HeaderOffset + 3
def account8RentEpochOffset : Nat :=
  account8HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account8ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8ExecutableOffset
def account8RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account8RentEpochOffset

/-- Seed octuple-skip+account-8 owner layout plus executable flag and rent_epoch. -/
def account8ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8)
    (key8Word : U64)
    (acc8Signer acc8Writable : U8)
    (acc8Lamports acc8DataLen : U64)
    (acc8Owner0 acc8Owner1 : U64)
    (acc8Owner2 acc8Owner3 : U64)
    (acc8Executable : U8) (acc8Rent : U64) : Option Mem := do
  let m₁ ← account8OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker
      key8Word
      acc8Signer acc8Writable
      acc8Lamports acc8DataLen
      acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3
  let m₂ ← storev .m8 m₁ account8ExecutableAddr (.vbyte acc8Executable)
  storev .m64 m₂ account8RentEpochAddr (.vlong acc8Rent)

/-- Typed octuple skip then account-8 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount8ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [

    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run octuple skip+account-8 walk against seeded input memory. -/
def evalWalkAccount8ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-8 executable and rent_epoch. -/
def evalAbsAccount8ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account8ExecutableAddr
  let rentEpoch ← loadv .m64 memory account8RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

/-- Walked account-8 assembly after skip chain is well-formed. -/
theorem walkAccount8ExecRentAfterSkipChain_verified :
    (walkAccount8ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete octuple skip+exec/rent: executable=`1`, rent=`0xF3`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount8_after_skip_executable_1_rent_0xF3 :
    (do
      let mem ← account8ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker
          0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
      let (regs, finalMem) ← evalWalkAccount8ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF3 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-8 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount8ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB3 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4
          0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
      let (regs, _) ← evalWalkAccount8ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount8ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF3)) =
      some true := by
  native_decide

/-!
## E-infinity knife 65 - Loader account-8 → account-9 marker skip chain (`svm-sem-070`)

Knife 64 completes account-8 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-8 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5/6/7/8 skip chain with an account-8 zero-dataLen skip
and proves the loaded account-9 marker matches an absolute `r6`-relative load. Still not
account-9 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-9 dup marker after account-8 zero-dataLen rent. -/
def account9HeaderOffset : Nat := account8RentEpochOffset + 8
def account9HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9HeaderOffset

/-- Seed account-0/1/2/3/4/5/6/7/8 layout plus account-8 zero data_len and account-9 dup marker. -/
def account8SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) : Option Mem := do
  let m₁ ← account8ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
  let m₂ ← storev .m64 m₁ account8DataLenAddr (.vlong 0)
  storev .m8 m₂ account9HeaderAddr (.vbyte acc9Marker)

/-- Typed nonuple skip: account-0/1/2/3/4/5/6/7/8 zero-dataLen skips land on account-9 marker. -/
def walkAccount8SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5/6/7/8 skip-to-account-9-marker walk against seeded input memory. -/
def evalWalkAccount8SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount8SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-9 dup marker. -/
def evalAbsAccount9Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account9HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-8→account-9 skip-chain assembly is well-formed. -/
theorem walkAccount8SkipNextAfterSkipChain_verified :
    (walkAccount8SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-9 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount8_skip_next_marker_0xff :
    (do
      let mem ← account8SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount8SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-9 header. -/
theorem walkAccount8SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account8SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB5
      let (regs, _) ← evalWalkAccount8SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount9Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB5)) =
      some true := by
  native_decide

/-!
## E-infinity knife 66 - Loader account-9 header/key after skip chain (`svm-sem-071`)

Knife 65 proves the nonuple skip lands on the account-9 dup marker. Emit then treats that
address as the account-9 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6/7/8 skip chain with an account-9 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-9 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-9 first key limb. -/
def account9KeyOffset : Nat := account9HeaderOffset + 8
def account9KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9KeyOffset

/-- Seed nonuple-skip layout plus account-9 first key limb. -/
def account9MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) : Option Mem := do
  let m ← account8SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker
  storev .m64 m account9KeyAddr (.vlong key9Word)

/-- Typed nonuple skip then account-9 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount9MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 dup marker and first key limb. -/
def evalAbsAccount9Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account9HeaderAddr
  let key ← loadv .m64 memory account9KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

theorem walkAccount9MetaAfterSkipChain_verified :
    (walkAccount9MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+meta: marker=`0xff`, key=`0x79`, key staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_key_0x79 :
    (do
      let mem ← account9MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79
      let (regs, finalMem) ← evalWalkAccount9MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x79 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x79))) =
      some true := by
  native_decide

/-- Walked account-9 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79
      let (regs, _) ← evalWalkAccount9MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount9Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB6 && key == 0x79)) =
      some true := by
  native_decide

/-!
## E-infinity knife 67 - Loader account-9 signer/writable after skip chain (`svm-sem-072`)

Knife 66 lands the cursor on account-9 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the nonuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-9,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-9 signer and writable flag bytes. -/
def account9SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account9HeaderOffset + 1)
def account9WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account9HeaderOffset + 2)

/-- Seed nonuple-skip+account-9 meta layout plus signer/writable flags. -/
def account9FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8) : Option Mem := do
  let m₁ ← account9MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word
  let m₂ ← storev .m8 m₁ account9SignerAddr (.vbyte acc9Signer)
  storev .m8 m₂ account9WritableAddr (.vbyte acc9Writable)

/-- Typed nonuple skip then account-9 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount9FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 signer and writable flag bytes. -/
def evalAbsAccount9Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account9SignerAddr
  let writable ← loadv .m8 memory account9WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

theorem walkAccount9FlagsAfterSkipChain_verified :
    (walkAccount9FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_signer_writable_1 :
    (do
      let mem ← account9FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1
      let (regs, finalMem) ← evalWalkAccount9FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-9 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount9FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0
      let (regs, _) ← evalWalkAccount9FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount9Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 68 - Loader account-9 lamports/data_len after skip chain (`svm-sem-073`)

Knife 67 covers account-9 signer/writable after the skip chain. Emit then reads account-9
lamports and data_len (`+0x48` / `+0x50`). This knife composes the nonuple skip chain with
those word loads and proves agreement with absolute `r6`-relative loads. Still not owner/executable/rent
for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 lamports and data_len. -/
def account9LamportsOffset : Nat :=
  account9HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account9DataLenOffset : Nat :=
  account9HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account9LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9LamportsOffset
def account9DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9DataLenOffset

/-- Seed nonuple-skip+account-9 flags layout plus lamports and data_len words. -/
def account9BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64) : Option Mem := do
  let m₁ ← account9FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
  let m₂ ← storev .m64 m₁ account9LamportsAddr (.vlong acc9Lamports)
  storev .m64 m₂ account9DataLenAddr (.vlong acc9DataLen)

/-- Typed nonuple skip then account-9 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount9BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenFieldOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 dataLenFieldOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 lamports and data_len. -/
def evalAbsAccount9Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account9LamportsAddr
  let dataLen ← loadv .m64 memory account9DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

theorem walkAccount9BudgetAfterSkipChain_verified :
    (walkAccount9BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+budget: lamports=`9000`, data_len=`192`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_lamports_9000_dataLen_192 :
    (do
      let mem ← account9BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192
      let (regs, finalMem) ← evalWalkAccount9BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 9000 && regs .br2 == 192 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 9000))) =
      some true := by
  native_decide

/-- Walked account-9 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192
      let (regs, _) ← evalWalkAccount9BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount9Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 9000 && dataLen == 192)) =
      some true := by
  native_decide

/-!
## E-infinity knife 69 - Loader account-9 owner limbs 0/1 after skip chain (`svm-sem-074`)

Knife 68 completes account-9 lamports/data_len after the skip chain. Emit then reads account-9
owner pubkey limbs 0 and 1 (`+0x28` / `+0x30`). This knife composes the nonuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not owner
limbs 2/3 or exec/rent for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 owner limbs 0 and 1. -/
def account9Owner0Offset : Nat :=
  account9HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account9Owner1Offset : Nat :=
  account9HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account9Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner0Offset
def account9Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner1Offset

/-- Seed nonuple-skip+account-9 budget layout plus owner limbs 0/1. -/
def account9OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64) : Option Mem := do
  let m₁ ← account9BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen
  let m₂ ← storev .m64 m₁ account9Owner0Addr (.vlong acc9Owner0)
  storev .m64 m₂ account9Owner1Addr (.vlong acc9Owner1)

/-- Typed nonuple skip then account-9 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount9OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 owner limbs 0 and 1. -/
def evalAbsAccount9Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account9Owner0Addr
  let owner1 ← loadv .m64 memory account9Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

theorem walkAccount9OwnerAfterSkipChain_verified :
    (walkAccount9OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+owner lo: owner0=`0xEC`, owner1=`0xFD`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_owner0_0xEC_owner1_0xFD :
    (do
      let mem ← account9OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD
      let (regs, finalMem) ← evalWalkAccount9OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xEC && regs .br2 == 0xFD &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xEC))) =
      some true := by
  native_decide

/-- Walked account-9 owner lo after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD
      let (regs, _) ← evalWalkAccount9OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount9Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xEC && owner1 == 0xFD)) =
      some true := by
  native_decide

/-!
## E-infinity knife 70 - Loader account-9 owner limbs 2/3 after skip chain (`svm-sem-075`)

Knife 69 completes account-9 owner limbs 0/1 after the skip chain. Emit then reads account-9
owner pubkey limbs 2 and 3 (`+0x38` / `+0x40`). This knife composes the nonuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not
exec/rent for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 owner limbs 2 and 3. -/
def account9Owner2Offset : Nat :=
  account9HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account9Owner3Offset : Nat :=
  account9HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account9Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner2Offset
def account9Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner3Offset

/-- Seed nonuple-skip+account-9 owner layout plus owner limbs 2/3. -/
def account9OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64)
    (acc9Owner2 acc9Owner3 : U64) : Option Mem := do
  let m₁ ← account9OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1
  let m₂ ← storev .m64 m₁ account9Owner2Addr (.vlong acc9Owner2)
  storev .m64 m₂ account9Owner3Addr (.vlong acc9Owner3)

/-- Typed nonuple skip then account-9 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount9OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 owner limbs 2 and 3. -/
def evalAbsAccount9OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account9Owner2Addr
  let owner3 ← loadv .m64 memory account9Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

theorem walkAccount9OwnerHiAfterSkipChain_verified :
    (walkAccount9OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+owner hi: owner2=`0x1E`, owner3=`0x2F`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_owner2_0x1E_owner3_0x2F :
    (do
      let mem ← account9OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F
      let (regs, finalMem) ← evalWalkAccount9OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1E && regs .br2 == 0x2F &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1E))) =
      some true := by
  native_decide

/-- Walked account-9 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F
      let (regs, _) ← evalWalkAccount9OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount9OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1E && owner3 == 0x2F)) =
      some true := by
  native_decide

/-!
## E-infinity knife 71 - Loader account-9 executable + rent_epoch after skip chain (`svm-sem-076`)

Knife 70 completes account-9 owner pubkey after the skip chain. Emit then reads account-9
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the nonuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 executable and zero-dataLen rent_epoch. -/
def account9ExecutableOffset : Nat := account9HeaderOffset + 3
def account9RentEpochOffset : Nat :=
  account9HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account9ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9ExecutableOffset
def account9RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9RentEpochOffset

/-- Seed nonuple-skip+account-9 owner layout plus executable flag and rent_epoch. -/
def account9ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64)
    (acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64) : Option Mem := do
  let m₁ ← account9OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3
  let m₂ ← storev .m8 m₁ account9ExecutableAddr (.vbyte acc9Executable)
  storev .m64 m₂ account9RentEpochAddr (.vlong acc9Rent)

/-- Typed nonuple skip then account-9 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount9ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 executable and rent_epoch. -/
def evalAbsAccount9ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account9ExecutableAddr
  let rentEpoch ← loadv .m64 memory account9RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

theorem walkAccount9ExecRentAfterSkipChain_verified :
    (walkAccount9ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+exec/rent: executable=`1`, rent=`0xF4`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_executable_1_rent_0xF4 :
    (do
      let mem ← account9ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4
      let (regs, finalMem) ← evalWalkAccount9ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-9 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4
      let (regs, _) ← evalWalkAccount9ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount9ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF4)) =
      some true := by
  native_decide

/-!
## E-infinity knife 72 - Loader account-9 → account-10 marker skip chain (`svm-sem-077`)

Knife 71 completes account-9 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-9 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5/6/7/8/9 skip chain with an account-9 zero-dataLen skip
and proves the loaded account-10 marker matches an absolute `r6`-relative load. Still not
account-10 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-10 dup marker after account-9 zero-dataLen rent. -/
def account10HeaderOffset : Nat := account9RentEpochOffset + 8
def account10HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10HeaderOffset

/-- Seed account-0/1/2/3/4/5/6/7/8/9 layout plus account-9 zero data_len and account-10 dup marker. -/
def account9SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64) (acc10Marker : U8) : Option Mem := do
  let m₁ ← account9ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
  let m₂ ← storev .m64 m₁ account9DataLenAddr (.vlong 0)
  storev .m8 m₂ account10HeaderAddr (.vbyte acc10Marker)

/-- Typed decuple skip: account-0/1/2/3/4/5/6/7/8/9 zero-dataLen skips land on account-10 marker. -/
def walkAccount9SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5/6/7/8/9 skip-to-account-10-marker walk against seeded input memory. -/
def evalWalkAccount9SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-10 dup marker. -/
def evalAbsAccount10Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account10HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

/-- Walked account-9→account-10 skip-chain assembly is well-formed. -/
theorem walkAccount9SkipNextAfterSkipChain_verified :
    (walkAccount9SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete chained skip: account-10 marker=`0xff`, staged at `[r10-16]`. -/
theorem evalWalkAccount9_skip_next_marker_0xff :
    (do
      let mem ← account9SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount9SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

/-- Chained skip marker agrees with absolute `r6`-relative load at account-10 header. -/
theorem walkAccount9SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB7
      let (regs, _) ← evalWalkAccount9SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount10Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB7)) =
      some true := by
  native_decide


/-!
## E-infinity knife 73 - Loader account-10 header/key after skip chain (`svm-sem-078`)

Knife 72 proves the decuple skip lands on the account-10 dup marker. Emit then treats that
address as the account-10 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6/7/8/9 skip chain with an account-10 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-10 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-10 first key limb. -/
def account10KeyOffset : Nat := account10HeaderOffset + 8
def account10KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10KeyOffset

/-- Seed decuple-skip layout plus account-10 first key limb. -/
def account10MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64) : Option Mem := do
  let m ← account9SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker
  storev .m64 m account10KeyAddr (.vlong key10Word)

/-- Typed decuple skip then account-10 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount10MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 dup marker and first key limb. -/
def evalAbsAccount10Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account10HeaderAddr
  let key ← loadv .m64 memory account10KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

theorem walkAccount10MetaAfterSkipChain_verified :
    (walkAccount10MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+meta: marker=`0xff`, key=`0x7A`, key staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_key_0x7A :
    (do
      let mem ← account10MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A
      let (regs, finalMem) ← evalWalkAccount10MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x7A &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x7A))) =
      some true := by
  native_decide

/-- Walked account-10 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount10MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A
      let (regs, _) ← evalWalkAccount10MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount10Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB8 && key == 0x7A)) =
      some true := by
  native_decide


/-!
## E-infinity knife 74 - Loader account-10 signer/writable after skip chain (`svm-sem-079`)

Knife 73 lands the cursor on account-10 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the decuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-10,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-10 signer and writable flag bytes. -/
def account10SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account10HeaderOffset + 1)
def account10WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account10HeaderOffset + 2)

/-- Seed decuple-skip+account-10 meta layout plus signer/writable flags. -/
def account10FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8) : Option Mem := do
  let m₁ ← account10MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word
  let m₂ ← storev .m8 m₁ account10SignerAddr (.vbyte acc10Signer)
  storev .m8 m₂ account10WritableAddr (.vbyte acc10Writable)

/-- Typed decuple skip then account-10 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount10FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 signer and writable flag bytes. -/
def evalAbsAccount10Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account10SignerAddr
  let writable ← loadv .m8 memory account10WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

theorem walkAccount10FlagsAfterSkipChain_verified :
    (walkAccount10FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_signer_writable_1 :
    (do
      let mem ← account10FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1
      let (regs, finalMem) ← evalWalkAccount10FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-10 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount10FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0
      let (regs, _) ← evalWalkAccount10FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount10Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide


/-!
## E-infinity knife 75 - Loader account-10 lamports/data_len after skip chain (`svm-sem-080`)

Knife 74 covers account-10 signer/writable after the skip chain. Emit then reads account-10
lamports and data_len (`+0x48` / `+0x50`). This knife composes the decuple skip chain with
those word loads and proves agreement with absolute `r6`-relative loads. Still not owner/executable/rent
for account-10, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-10 lamports and data_len. -/
def account10LamportsOffset : Nat :=
  account10HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account10DataLenOffset : Nat :=
  account10HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account10LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10LamportsOffset
def account10DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10DataLenOffset

/-- Seed decuple-skip+account-10 flags layout plus lamports and data_len words. -/
def account10BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64) : Option Mem := do
  let m₁ ← account10FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
  let m₂ ← storev .m64 m₁ account10LamportsAddr (.vlong acc10Lamports)
  storev .m64 m₂ account10DataLenAddr (.vlong acc10DataLen)

/-- Typed decuple skip then account-10 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount10BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenFieldOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 dataLenFieldOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 lamports and data_len. -/
def evalAbsAccount10Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account10LamportsAddr
  let dataLen ← loadv .m64 memory account10DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

theorem walkAccount10BudgetAfterSkipChain_verified :
    (walkAccount10BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+budget: lamports=`10000`, data_len=`208`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_lamports_10000_dataLen_208 :
    (do
      let mem ← account10BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208
      let (regs, finalMem) ← evalWalkAccount10BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 10000 && regs .br2 == 208 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 10000))) =
      some true := by
  native_decide

/-- Walked account-10 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount10BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208
      let (regs, _) ← evalWalkAccount10BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount10Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 10000 && dataLen == 208)) =
      some true := by
  native_decide


/-!
## E-infinity knife 76 - Loader account-10 owner limbs 0/1 after skip chain (`svm-sem-081`)

Knife 75 completes account-10 lamports/data_len after the skip chain. Emit then reads account-10
owner pubkey limbs 0 and 1 (`+0x28` / `+0x30`). This knife composes the decuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not owner
limbs 2/3 or exec/rent for account-10, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-10 owner limbs 0 and 1. -/
def account10Owner0Offset : Nat :=
  account10HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account10Owner1Offset : Nat :=
  account10HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account10Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10Owner0Offset
def account10Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10Owner1Offset

/-- Seed decuple-skip+account-10 budget layout plus owner limbs 0/1. -/
def account10OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64) : Option Mem := do
  let m₁ ← account10BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen
  let m₂ ← storev .m64 m₁ account10Owner0Addr (.vlong acc10Owner0)
  storev .m64 m₂ account10Owner1Addr (.vlong acc10Owner1)

/-- Typed decuple skip then account-10 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount10OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 owner limbs 0 and 1. -/
def evalAbsAccount10Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account10Owner0Addr
  let owner1 ← loadv .m64 memory account10Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

theorem walkAccount10OwnerAfterSkipChain_verified :
    (walkAccount10OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+owner lo: owner0=`0xED`, owner1=`0xFE`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_owner0_0xED_owner1_0xFE :
    (do
      let mem ← account10OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE
      let (regs, finalMem) ← evalWalkAccount10OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xED && regs .br2 == 0xFE &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xED))) =
      some true := by
  native_decide

/-- Walked account-10 owner lo after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount10OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE
      let (regs, _) ← evalWalkAccount10OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount10Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xED && owner1 == 0xFE)) =
      some true := by
  native_decide


/-!
## E-infinity knife 77 - Loader account-10 owner limbs 2/3 after skip chain (`svm-sem-082`)

Knife 76 completes account-10 owner limbs 0/1 after the skip chain. Emit then reads account-10
owner pubkey limbs 2 and 3 (`+0x38` / `+0x40`). This knife composes the decuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not
exec/rent for account-10, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-10 owner limbs 2 and 3. -/
def account10Owner2Offset : Nat :=
  account10HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account10Owner3Offset : Nat :=
  account10HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account10Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10Owner2Offset
def account10Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10Owner3Offset

/-- Seed decuple-skip+account-10 owner lo layout plus owner limbs 2/3. -/
def account10OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64) : Option Mem := do
  let m₁ ← account10OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1
  let m₂ ← storev .m64 m₁ account10Owner2Addr (.vlong acc10Owner2)
  storev .m64 m₂ account10Owner3Addr (.vlong acc10Owner3)

/-- Typed decuple skip then account-10 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount10OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 owner limbs 2 and 3. -/
def evalAbsAccount10OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account10Owner2Addr
  let owner3 ← loadv .m64 memory account10Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

theorem walkAccount10OwnerHiAfterSkipChain_verified :
    (walkAccount10OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+owner hi: owner2=`0x1F`, owner3=`0x30`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_owner2_0x1F_owner3_0x30 :
    (do
      let mem ← account10OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30
      let (regs, finalMem) ← evalWalkAccount10OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1F && regs .br2 == 0x30 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1F))) =
      some true := by
  native_decide

/-- Walked account-10 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount10OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30
      let (regs, _) ← evalWalkAccount10OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount10OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1F && owner3 == 0x30)) =
      some true := by
  native_decide


/-!
## E-infinity knife 78 - Loader account-10 executable + rent_epoch after skip chain (`svm-sem-083`)

Knife 77 completes account-10 owner pubkey after the skip chain. Emit then reads account-10
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the decuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-10 executable and zero-dataLen rent_epoch. -/
def account10ExecutableOffset : Nat := account10HeaderOffset + 3
def account10RentEpochOffset : Nat :=
  account10HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account10ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10ExecutableOffset
def account10RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account10RentEpochOffset

/-- Seed decuple-skip+account-10 owner layout plus executable flag and rent_epoch. -/
def account10ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) : Option Mem := do
  let m₁ ← account10OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
  let m₂ ← storev .m8 m₁ account10ExecutableAddr (.vbyte acc10Executable)
  storev .m64 m₂ account10RentEpochAddr (.vlong acc10Rent)

/-- Typed decuple skip then account-10 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount10ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run decuple skip+account-10 walk against seeded input memory. -/
def evalWalkAccount10ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-10 executable and rent_epoch. -/
def evalAbsAccount10ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account10ExecutableAddr
  let rentEpoch ← loadv .m64 memory account10RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

theorem walkAccount10ExecRentAfterSkipChain_verified :
    (walkAccount10ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete decuple skip+exec/rent: executable=`1`, rent=`0xF5`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount10_after_skip_executable_1_rent_0xF5 :
    (do
      let mem ← account10ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5
      let (regs, finalMem) ← evalWalkAccount10ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF5 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-10 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount10ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5
      let (regs, _) ← evalWalkAccount10ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount10ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF5)) =
      some true := by
  native_decide

/-!
## E-infinity knife 79 - Loader account-10 → account-11 marker skip chain (`svm-sem-084`)

Knife 78 completes account-10 fields after the skip chain. Emit chains the same
`emitSkipAccount` geometry from the account-10 header cursor to reach the next dup marker.
This knife composes the account-0/1/2/3/4/5/6/7/8/9/10 skip chain with an account-10 zero-dataLen skip
and proves the loaded account-11 marker matches an absolute `r6`-relative load. Still not
account-11 meta fields, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offset/VA of account-11 dup marker after account-10 zero-dataLen rent. -/
def account11HeaderOffset : Nat := account10RentEpochOffset + 8
def account11HeaderAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11HeaderOffset

/-- Seed account-0/1/2/3/4/5/6/7/8/9/10 layout plus account-10 zero data_len and account-11 dup marker. -/
def account10SkipNextInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) : Option Mem := do
  let m₁ ← account10ExecRentInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent
  let m₂ ← storev .m64 m₁ account10DataLenAddr (.vlong 0)
  storev .m8 m₂ account11HeaderAddr (.vbyte acc11Marker)

/-- Typed undecuple skip: account-0/1/2/3/4/5/6/7/8/9/10 zero-dataLen skips land on account-11 marker. -/
def walkAccount10SkipNextAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .st .m64 .br10 (.reg .br1) stackOff]

/-- Run chained account-0/1/2/3/4/5/6/7/8/9/10 skip-to-account-11-marker walk against seeded input memory. -/
def evalWalkAccount10SkipNextAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount10SkipNextAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative load of the account-11 dup marker. -/
def evalAbsAccount11Marker? (memory : Mem) : Option U8 := do
  let marker ← loadv .m8 memory account11HeaderAddr
  match marker with
  | .vbyte m => some m
  | _ => none

theorem walkAccount10SkipNextAfterSkipChain_verified :
    (walkAccount10SkipNextAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount10_skip_next_marker_0xff :
    (do
      let mem ← account10SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker
      let (regs, finalMem) ← evalWalkAccount10SkipNextAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xff))) =
      some true := by
  native_decide

theorem walkAccount10SkipNextAfterSkipChain_eq_absLoad :
    (do
      let mem ← account10SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9
      let (regs, _) ← evalWalkAccount10SkipNextAfterSkipChainToStack? rhsStackOffset mem
      let marker ← evalAbsAccount11Marker? mem
      pure (regs .br1 == marker.setWidth 64 && marker == 0xB9)) =
      some true := by
  native_decide


/-!
## E-infinity knife 80 - Loader account-11 header/key after skip chain (`svm-sem-085`)

Knife 79 proves the undecuple skip lands on the account-11 dup marker. Emit then treats that
address as the account-11 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6/7/8/9/10 skip chain with an account-11 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-11 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-11 first key limb. -/
def account11KeyOffset : Nat := account11HeaderOffset + 8
def account11KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11KeyOffset

/-- Seed undecuple-skip layout plus account-11 first key limb. -/
def account11MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64) : Option Mem := do
  let m ← account10SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker
  storev .m64 m account11KeyAddr (.vlong key11Word)

/-- Typed undecuple skip then account-11 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount11MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]

def evalWalkAccount11MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account11HeaderAddr
  let key ← loadv .m64 memory account11KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

theorem walkAccount11MetaAfterSkipChain_verified :
    (walkAccount11MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_key_0x7B :
    (do
      let mem ← account11MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B
      let (regs, finalMem) ← evalWalkAccount11MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x7B &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x7B))) =
      some true := by
  native_decide

theorem walkAccount11MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B
      let (regs, _) ← evalWalkAccount11MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount11Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB9 && key == 0x7B)) =
      some true := by
  native_decide


/-!
## E-infinity knife 81 - Loader account-11 signer/writable after skip chain (`svm-sem-086`)

Knife 80 lands the cursor on account-11 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the undecuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-11,
full vectors, syscalls, CPI, or ELF accept.
-/

def account11SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account11HeaderOffset + 1)
def account11WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account11HeaderOffset + 2)

def account11FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64)
    (acc11Signer acc11Writable : U8) : Option Mem := do
  let m₁ ← account11MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker key11Word
  let m₂ ← storev .m8 m₁ account11SignerAddr (.vbyte acc11Signer)
  storev .m8 m₂ account11WritableAddr (.vbyte acc11Writable)

/-- Typed undecuple skip then account-11 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount11FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

def evalWalkAccount11FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account11SignerAddr
  let writable ← loadv .m8 memory account11WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

theorem walkAccount11FlagsAfterSkipChain_verified :
    (walkAccount11FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_signer_writable_1 :
    (do
      let mem ← account11FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B 1 1
      let (regs, finalMem) ← evalWalkAccount11FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

theorem walkAccount11FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B 1 0
      let (regs, _) ← evalWalkAccount11FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount11Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide


/-!
## E-infinity knife 82 - Loader account-11 lamports/data_len after skip chain (`svm-sem-087`)
-/

def account11LamportsOffset : Nat :=
  account11HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account11DataLenOffset : Nat :=
  account11HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account11LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11LamportsOffset
def account11DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11DataLenOffset

def account11BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64)
    (acc11Signer acc11Writable : U8)
    (acc11Lamports acc11DataLen : U64) : Option Mem := do
  let m₁ ← account11FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker key11Word acc11Signer acc11Writable
  let m₂ ← storev .m64 m₁ account11LamportsAddr (.vlong acc11Lamports)
  storev .m64 m₂ account11DataLenAddr (.vlong acc11DataLen)

/-- Typed undecuple skip then account-11 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount11BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenFieldOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 dataLenFieldOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

def evalWalkAccount11BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account11LamportsAddr
  let dataLen ← loadv .m64 memory account11DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

theorem walkAccount11BudgetAfterSkipChain_verified :
    (walkAccount11BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_lamports_11000_dataLen_224 :
    (do
      let mem ← account11BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B 1 1 11000 224
      let (regs, finalMem) ← evalWalkAccount11BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 11000 && regs .br2 == 224 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 11000))) =
      some true := by
  native_decide

theorem walkAccount11BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B 1 0 11000 224
      let (regs, _) ← evalWalkAccount11BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount11Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 11000 && dataLen == 224)) =
      some true := by
  native_decide


/-!
## E-infinity knife 83 - Loader account-11 owner limbs 0/1 after skip chain (`svm-sem-088`)
-/

def account11Owner0Offset : Nat :=
  account11HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account11Owner1Offset : Nat :=
  account11HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account11Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11Owner0Offset
def account11Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11Owner1Offset

def account11OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64)
    (acc11Signer acc11Writable : U8)
    (acc11Lamports acc11DataLen : U64)
    (acc11Owner0 acc11Owner1 : U64) : Option Mem := do
  let m₁ ← account11BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker key11Word acc11Signer acc11Writable
      acc11Lamports acc11DataLen
  let m₂ ← storev .m64 m₁ account11Owner0Addr (.vlong acc11Owner0)
  storev .m64 m₂ account11Owner1Addr (.vlong acc11Owner1)

/-- Typed undecuple skip then account-11 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount11OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

def evalWalkAccount11OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account11Owner0Addr
  let owner1 ← loadv .m64 memory account11Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

theorem walkAccount11OwnerAfterSkipChain_verified :
    (walkAccount11OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_owner0_0xEE_owner1_0xFF :
    (do
      let mem ← account11OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B 1 1 11000 224 0xEE 0xFF
      let (regs, finalMem) ← evalWalkAccount11OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xEE && regs .br2 == 0xFF &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xEE))) =
      some true := by
  native_decide

theorem walkAccount11OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B 1 0 11000 224 0xEE 0xFF
      let (regs, _) ← evalWalkAccount11OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount11Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xEE && owner1 == 0xFF)) =
      some true := by
  native_decide


/-!
## E-infinity knife 84 - Loader account-11 owner limbs 2/3 after skip chain (`svm-sem-089`)
-/

def account11Owner2Offset : Nat :=
  account11HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account11Owner3Offset : Nat :=
  account11HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account11Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11Owner2Offset
def account11Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11Owner3Offset

def account11OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64)
    (acc11Signer acc11Writable : U8)
    (acc11Lamports acc11DataLen : U64)
    (acc11Owner0 acc11Owner1 : U64)
    (acc11Owner2 acc11Owner3 : U64) : Option Mem := do
  let m₁ ← account11OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker key11Word acc11Signer acc11Writable
      acc11Lamports acc11DataLen acc11Owner0 acc11Owner1
  let m₂ ← storev .m64 m₁ account11Owner2Addr (.vlong acc11Owner2)
  storev .m64 m₂ account11Owner3Addr (.vlong acc11Owner3)

/-- Typed undecuple skip then account-11 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount11OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

def evalWalkAccount11OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account11Owner2Addr
  let owner3 ← loadv .m64 memory account11Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

theorem walkAccount11OwnerHiAfterSkipChain_verified :
    (walkAccount11OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_owner2_0x20_owner3_0x31 :
    (do
      let mem ← account11OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B 1 1 11000 224 0xEE 0xFF 0x20 0x31
      let (regs, finalMem) ← evalWalkAccount11OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x20 && regs .br2 == 0x31 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x20))) =
      some true := by
  native_decide

theorem walkAccount11OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B 1 0 11000 224 0xEE 0xFF 0x20 0x31
      let (regs, _) ← evalWalkAccount11OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount11OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x20 && owner3 == 0x31)) =
      some true := by
  native_decide


/-!
## E-infinity knife 85 - Loader account-11 executable + rent_epoch after skip chain (`svm-sem-090`)
-/

def account11ExecutableOffset : Nat := account11HeaderOffset + 3
def account11RentEpochOffset : Nat :=
  account11HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account11ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11ExecutableOffset
def account11RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account11RentEpochOffset

def account11ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64)
    (acc10Marker : U8) (key10Word : U64)
    (acc10Signer acc10Writable : U8)
    (acc10Lamports acc10DataLen : U64)
    (acc10Owner0 acc10Owner1 : U64)
    (acc10Owner2 acc10Owner3 : U64)
    (acc10Executable : U8) (acc10Rent : U64) (acc11Marker : U8) (key11Word : U64)
    (acc11Signer acc11Writable : U8)
    (acc11Lamports acc11DataLen : U64)
    (acc11Owner0 acc11Owner1 : U64)
    (acc11Owner2 acc11Owner3 : U64)
    (acc11Executable : U8) (acc11Rent : U64) : Option Mem := do
  let m₁ ← account11OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent
      acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3 acc9Executable acc9Rent
      acc10Marker key10Word acc10Signer acc10Writable
      acc10Lamports acc10DataLen acc10Owner0 acc10Owner1 acc10Owner2 acc10Owner3
      acc10Executable acc10Rent acc11Marker key11Word acc11Signer acc11Writable
      acc11Lamports acc11DataLen acc11Owner0 acc11Owner1 acc11Owner2 acc11Owner3
  let m₂ ← storev .m8 m₁ account11ExecutableAddr (.vbyte acc11Executable)
  storev .m64 m₂ account11RentEpochAddr (.vlong acc11Rent)

/-- Typed undecuple skip then account-11 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount11ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]

def evalWalkAccount11ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount11ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

def evalAbsAccount11ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account11ExecutableAddr
  let rentEpoch ← loadv .m64 memory account11RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

theorem walkAccount11ExecRentAfterSkipChain_verified :
    (walkAccount11ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

theorem evalWalkAccount11_after_skip_executable_1_rent_0xF6 :
    (do
      let mem ← account11ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker 0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 account0NonDupMarker 0x7A 1 1 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 account0NonDupMarker 0x7B 1 1 11000 224 0xEE 0xFF 0x20 0x31 1 0xF6
      let (regs, finalMem) ← evalWalkAccount11ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF6 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

theorem walkAccount11ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account11ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4 0xB8 0x7A 1 0 10000 208 0xED 0xFE 0x1F 0x30 1 0xF5 0xB9 0x7B 1 0 11000 224 0xEE 0xFF 0x20 0x31 1 0xF6
      let (regs, _) ← evalWalkAccount11ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount11ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF6)) =
      some true := by
  native_decide

end ProofForge.Svm.Solanalib
