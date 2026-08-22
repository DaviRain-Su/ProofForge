import SolanaLean.Golden
import SolanaLean.Evm.IR

namespace SolanaLean.Evm.Golden

open SolanaLean.Evm

/-- 竖切夹具：无 SVM 叶子。窄槽 / Option 双叶已开。 -/
def sources : Array SolanaLean.IR.Program := #[
  SolanaLean.Golden.extractedCounter,
  SolanaLean.Golden.extractedPair,
  SolanaLean.Golden.extractedWindow,
  SolanaLean.Golden.extractedPhase,
  SolanaLean.Golden.extractedFlag,
  SolanaLean.Golden.extractedMaybe
]

def programs : Array IR.Program :=
  sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end SolanaLean.Evm.Golden
