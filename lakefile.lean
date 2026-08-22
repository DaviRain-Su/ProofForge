import Lake
open Lake DSL

package «solana-lean» where
  version := v!"0.0.1"

@[default_target]
lean_lib SolanaLean

lean_lib Examples

lean_lib Tests
