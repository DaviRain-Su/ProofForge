import ProofForge.Svm.Emit
import ProofForge.Svm.IRCompat

namespace ProofForge.Svm.Emit

/-- Compatibility entry point for legacy fixtures and callers. -/
def emitCounterAsm (program : Extract.Legacy.Program) : Except String String := do
  emitAsm (← IR.fromProgram program)

end ProofForge.Svm.Emit
