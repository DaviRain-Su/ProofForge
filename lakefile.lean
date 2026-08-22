import Lake
open Lake DSL

package «solana-lean» where
  version := v!"0.0.1"

@[default_target]
lean_lib SolanaLean

lean_lib Examples

lean_lib Tests

lean_exe solanaLeanAssemble where
  root := `SolanaLean.AssembleMain

lean_exe evmLeanAssemble where
  root := `SolanaLean.Evm.AssembleMain
