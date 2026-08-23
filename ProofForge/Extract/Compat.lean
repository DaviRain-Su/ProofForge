import ProofForge.Extract
import ProofForge.Extract.LegacyAdapter

namespace ProofForge.Extract

/-- Compatibility adapter for callers that still consume the old closed-union program. -/
def extractProgram (env : Lean.Environment)
    (initName incrementName getName : Lean.Name)
    (programName : Option String := none)
    (fields? : Option (Array String) := none) :
    Except String Legacy.Program := do
  IR.toLegacyProgram (← extractProgramIR env initName incrementName getName programName fields?)

def extractCounter := extractProgram

/-- Compatibility adapter for callers that still consume the old closed-union program. -/
def extractModule (env : Lean.Environment) (ns : Lean.Name)
    (fields? : Option (Array String) := none) :
    Except String Legacy.Program := do
  IR.toLegacyProgram (← extractModuleIR env ns fields?)

end ProofForge.Extract
