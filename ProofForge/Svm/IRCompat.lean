import ProofForge.Svm.IR
import ProofForge.Extract.LegacyAdapter

namespace ProofForge.Svm.IR

/-- Compatibility adapter for callers that still own the old closed-union program. -/
def fromProgram (src : Extract.Legacy.Program) : Except String Program :=
  Extract.IR.ofLegacyProgram src >>= fromExtracted

end ProofForge.Svm.IR
