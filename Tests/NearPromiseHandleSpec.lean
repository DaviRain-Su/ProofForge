import ProofForge
import ProofForge.Wasm.Near.IR
import Examples.NearPromiseHandle

open Lean Elab Command

elab "#pf_guard_near_promise_handle" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearPromiseHandle with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless program.entries.any (·.ixName == "sendHandleThen") do
    throwError "NEAR PromiseHandle fixture missing sendHandleThen entry"
  logInfo m!"proofforge-near-promise-handle: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_promise_handle

#guard ProofForge.Wasm.Near.Sdk.Promises.defaultMaxFanIn == 4
#guard ProofForge.Wasm.Near.Sdk.Promises.maxPromiseDepth == 8
#guard Examples.NearPromiseHandle.handleDepthSmoke
