import SolanaLean.Golden
import SolanaLean.Evm.IR

namespace SolanaLean.Evm.Golden

open SolanaLean.Evm

/-- 竖切夹具：只钉无 SVM 叶子、全 UInt64 的例子。 -/
def sources : Array SolanaLean.IR.Program := #[
  SolanaLean.Golden.extractedCounter,
  SolanaLean.Golden.extractedPair,
  SolanaLean.Golden.extractedWindow,
  SolanaLean.Golden.extractedPhase
]

def programs : Array IR.Program :=
  sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end SolanaLean.Evm.Golden
