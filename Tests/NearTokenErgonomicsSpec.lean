import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.NearTokenErgonomics

open Lean Elab Command

elab "#pf_guard_near_token_ergonomics" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearTokenErgonomics none with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"canAddViaHelper\")", "(func (export \"addViaHelperW0\")",
      "(func (export \"addViaAndThen\")", "(func (export \"touch\")", "i64.add", "i64.lt_u"] do
    unless wat.contains anchor do
      throwError s!"NEAR token ergonomics WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-token-ergonomics: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_token_ergonomics
#pf_near_build Examples.NearTokenErgonomics

#guard ProofForge.Wasm.Near.Registry.digestOf "NearTokenErgonomics" ==
  some "cfc8d03d4e1883a5"
