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

end ProofForge.Svm.Solanalib
