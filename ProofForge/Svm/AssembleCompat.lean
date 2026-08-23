import ProofForge.Svm.Assemble
import ProofForge.Svm.IRCompat

namespace ProofForge.Svm.Assemble

/-- Compatibility entry point for callers that still own the old extraction IR. -/
def assembleProgram (outDir : System.FilePath) (program : Extract.Legacy.Program) : IO Result := do
  let lowered ← match IR.fromProgram program with
    | .error reason => throw <| IO.userError reason
    | .ok lowered => pure lowered
  assembleIRProgram outDir lowered

def assembleCounter (outDir : System.FilePath) (program : Extract.Legacy.Program) :
    IO Result :=
  assembleProgram outDir program

end ProofForge.Svm.Assemble
