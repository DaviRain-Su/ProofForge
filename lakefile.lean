import Lake
open Lake DSL

package «proofforge» where
  version := v!"0.0.1"

require solanalib from git
  "https://github.com/solana-foundation/leanprover-solanalib.git" @
  "6c115ef1ef6a0cde8dbd6fd875b7dc87d60939ec"

@[default_target]
lean_lib ProofForge

lean_lib Examples

lean_lib Tests

lean_exe pfAssemble where
  root := `ProofForge.Svm.AssembleMain

lean_exe pfEvmAssemble where
  root := `ProofForge.Evm.AssembleMain

lean_exe pf where
  root := `ProofForge.Cli
  supportInterpreter := true
