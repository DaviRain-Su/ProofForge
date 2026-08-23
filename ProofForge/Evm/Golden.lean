import ProofForge.Extract.LegacyGolden
import ProofForge.Evm.IRCompat

namespace ProofForge.Evm.Golden

open ProofForge.Evm

/-- 竖切夹具：无 SVM 叶子。窄槽 / Option 双叶已开。 -/
def sources : Array Extract.Legacy.Program := #[
  ProofForge.Golden.extractedCounter,
  ProofForge.Golden.extractedPair,
  ProofForge.Golden.extractedWindow,
  ProofForge.Golden.extractedPhase,
  ProofForge.Golden.extractedFlag,
  ProofForge.Golden.extractedMaybe,
  ProofForge.Golden.extractedEvmCtx,
  ProofForge.Golden.extractedTipJar,
  ProofForge.Golden.extractedLang,
  ProofForge.Golden.extractedVault,
  ProofForge.Golden.extractedOwnable,
  ProofForge.Golden.extractedToken
]

def programs : Array IR.Program :=
  sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end ProofForge.Evm.Golden
