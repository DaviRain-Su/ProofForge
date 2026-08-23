import ProofForge.Svm.Idl
import ProofForge.Svm.ABICompat

namespace ProofForge.Svm.Idl

private def sourceSlots (p : Extract.Legacy.Program) : Array Core.IR.Slot :=
  p.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def layoutDiscBytes (p : Extract.Legacy.Program) : Array Nat :=
  layoutDiscBytesOf (sourceSlots p)

/-- Compatibility entry point for the old extraction IR. -/
def emitIdl (p : Extract.Legacy.Program) : String :=
  let methods := p.methods.map fun method =>
    (method.kind, method.ixName, method.paramCount)
  emitIdlOf p.name (ABI.cpiAccountCount p) methods (sourceSlots p) (layoutDiscBytes p)

end ProofForge.Svm.Idl
