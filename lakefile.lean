import Lake
open Lake DSL

package «proofforge» where
  version := v!"0.0.1"

@[default_target]
lean_lib ProofForge

lean_lib Examples

lean_lib Projects

lean_lib Tests

lean_exe pfAssemble where
  root := `ProofForge.Svm.AssembleMain

lean_exe pfEvmAssemble where
  root := `ProofForge.Evm.AssembleMain

lean_exe pf where
  root := `ProofForge.Cli
