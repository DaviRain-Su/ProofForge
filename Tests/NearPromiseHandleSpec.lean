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
  unless program.entries.any (·.ixName == "sendHandleAnd3") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd3 entry"
  unless program.entries.any (·.ixName == "sendHandleAnd4") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd4 entry"
  unless program.entries.any (·.ixName == "sendHandleAnd5") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd5 entry"
  unless program.entries.any (·.ixName == "sendHandleAnd6") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd6 entry"
  unless program.entries.any (·.ixName == "sendHandleAnd7") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd7 entry"
  unless program.entries.any (·.ixName == "sendHandleAnd8") do
    throwError "NEAR PromiseHandle fixture missing sendHandleAnd8 entry"
  let sendHandleThen ← match program.entries.find? (·.ixName == "sendHandleThen") with
    | some method => pure method
    | none => throwError "missing sendHandleThen entry"
  let thenWat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleThen] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless thenWat.contains "(call $pf_promise_batch_then" do
    throwError "PromiseHandle thenReturned lost promise_batch_then"
  let sendHandleAnd3 ← match program.entries.find? (·.ixName == "sendHandleAnd3") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd3 entry"
  let and3Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd3] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and3Wat.contains "(call $pf_promise_and (local.get " &&
      and3Wat.contains "(i64.const 3)))" do
    throwError "PromiseHandle 3-way join lost promise_and count=3"
  let sendHandleAnd4 ← match program.entries.find? (·.ixName == "sendHandleAnd4") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd4 entry"
  let and4Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd4] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and4Wat.contains "(call $pf_promise_and (local.get " &&
      and4Wat.contains "(i64.const 4)))" do
    throwError "PromiseHandle 4-way join lost promise_and count=4"
  let sendHandleAnd5 ← match program.entries.find? (·.ixName == "sendHandleAnd5") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd5 entry"
  let and5Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd5] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and5Wat.contains "(call $pf_promise_and (local.get " &&
      and5Wat.contains "(i64.const 5)))" do
    throwError "PromiseHandle 5-way join lost promise_and count=5"
  let sendHandleAnd6 ← match program.entries.find? (·.ixName == "sendHandleAnd6") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd6 entry"
  let and6Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd6] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and6Wat.contains "(call $pf_promise_and (local.get " &&
      and6Wat.contains "(i64.const 6)))" do
    throwError "PromiseHandle 6-way join lost promise_and count=6"
  let sendHandleAnd7 ← match program.entries.find? (·.ixName == "sendHandleAnd7") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd7 entry"
  let and7Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd7] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and7Wat.contains "(call $pf_promise_and (local.get " &&
      and7Wat.contains "(i64.const 7)))" do
    throwError "PromiseHandle 7-way join lost promise_and count=7"
  let sendHandleAnd8 ← match program.entries.find? (·.ixName == "sendHandleAnd8") with
    | some method => pure method
    | none => throwError "missing sendHandleAnd8 entry"
  let and8Wat ← match ProofForge.Wasm.Near.Emit.emit { program with entries := #[sendHandleAnd8] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless and8Wat.contains "(call $pf_promise_and (local.get " &&
      and8Wat.contains "(i64.const 8)))" do
    throwError "PromiseHandle 8-way join lost promise_and count=8"
  logInfo m!"proofforge-near-promise-handle: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_promise_handle

#guard ProofForge.Wasm.Near.Sdk.Promises.defaultMaxFanIn == 4
#guard ProofForge.Wasm.Near.Sdk.Promises.maxPromiseDepth == 8
#guard Examples.NearPromiseHandle.handleDepthSmoke
#guard Examples.NearPromiseHandle.handleAnd5Smoke
#guard Examples.NearPromiseHandle.handleAnd8Smoke
