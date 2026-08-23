import ProofForge.Svm.IR
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
  let offset ← positiveOffset? (ProofForge.IR.acc0Data + slot.offset)
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
def checkedWriteFragment? (program : IR.Program) (write : Core.StateWrite) :
    Option CheckedWriteFragment := do
  let kind ← match write.value with | .checked kind _ _ => some kind | _ => none
  let store ← staticStoreAt? program write.place .br4
  return { compute := checkedArithBody kind, store }

/-- All instructions in the bounded arithmetic bridge satisfy Solanalib's v1 verifier. -/
theorem checkedArithBody_verified (kind : Core.CheckedArith) :
    (checkedArithBody kind).all (verifyInstr · version) = true := by
  cases kind <;> decide

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

/-- Execute one typed static-store instruction through Solanalib's memory semantics. -/
def evalStaticStore? (slot : IR.Slot) (regs : RegMap) (memory : Mem) : Option Mem := do
  let instruction ← staticStoreInstruction? slot
  match instruction with
  | .st chunk dst src offset => evalStore chunk dst src offset regs memory
  | _ => none

end ProofForge.Svm.Solanalib
