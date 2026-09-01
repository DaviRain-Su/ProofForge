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

end ProofForge.Svm.Solanalib
