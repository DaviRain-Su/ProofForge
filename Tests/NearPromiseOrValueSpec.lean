import Examples.NearPromiseOrValue
import Lean
import ProofForge

namespace Tests.NearPromiseOrValueSpec

open Lean Elab Command
open ProofForge.Wasm.Near

elab "#pf_near_promise_or_value_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearPromiseOrValue with
    | .ok program => pure program | .error reason => throwError reason
  let some sourceChoose := source.methods.find? (·.ixName == "choose")
    | throwError "missing source choose"
  unless sourceChoose.kind == .increment && sourceChoose.retCount == 2 &&
      sourceChoose.retSchema == .scalar .uint128 &&
      sourceChoose.annotations.contains "near.promise-or-value-u128.v1" do
    throwError m!"extractor lost nominal PromiseOrValueU128 frame: " ++
      m!"kind={repr sourceChoose.kind}, ret={repr sourceChoose.retSchema}/{sourceChoose.retCount}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let some choose := program.entries.find? (·.ixName == "choose")
    | throwError "missing target choose"
  unless choose.kind == .increment && choose.outputSchema == some (.scalar .uint128) &&
      choose.outputPolicy == "near-promise-or-json-u128-v1" && choose.tupleArity == some 2 do
    throwError s!"target lost dual terminal policy: {repr choose.outputSchema}/" ++
      s!"{choose.outputPolicy}/{repr choose.tupleArity}"
  let unannotated := { source with methods := source.methods.map fun method =>
    if method.ixName == "choose" then
      let annotations := method.annotations.filter fun annotation =>
        annotation != "near.promise-or-value-u128.v1"
      { method with annotations }
    else method }
  match IR.fromExtracted unannotated >>= Emit.emit with
  | .error reason =>
      unless reason.contains "JSON u128 output cannot also return a promise" do
        throwError s!"wrong unannotated Promise/u128 rejection: {reason}"
  | .ok _ => throwError "ordinary mutating U128 silently gained a Promise terminal"
  let malformed := { source with methods := source.methods.map fun method =>
    if method.ixName == "choose" then { method with retSchema := .scalar .uint64, retCount := 1 }
    else method }
  match IR.fromExtracted malformed with
  | .error reason =>
      unless reason.contains "requires an exact U128 result" do
        throwError s!"wrong Promise-or-u128 frame rejection: {reason}"
  | .ok _ => throwError "Promise-or-u128 annotation accepted a non-U128 result"
  let invalidPolicies := #[
    ({ source with methods := source.methods.map fun method =>
      if method.ixName == "choose" then { method with kind := .get } else method },
      "requires a mutating entry"),
    ({ source with methods := source.methods.map fun method =>
      if method.ixName == "choose" then
        { method with annotations := method.annotations.push "near.void.v1" }
      else method }, "cannot combine empty and Promise-or-u128 output")]
  for (invalid, expected) in invalidPolicies do
    match IR.fromExtracted invalid with
    | .error reason =>
        unless reason.contains expected do
          throwError s!"wrong Promise-or-u128 policy rejection: {reason}"
    | .ok _ => throwError "invalid Promise-or-u128 policy combination was accepted"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  let parts := wat.splitOn "(func (export \"choose\")"
  unless parts.length == 2 do throwError "choose must be exported exactly once"
  let body := (parts[1]!).splitOn "\n  (func (export" |>.head!
  unless (body.splitOn "(call $pf_value_return").length == 2 &&
      (body.splitOn "(call $pf_promise_return").length == 2 &&
      body.contains "(call $pf_u128_decimal" && body.contains "(call $pf_promise_batch_create" do
    throwError "dual terminal did not retain exactly one value and one Promise return branch"
  for terminal in #["(call $pf_value_return", "(call $pf_promise_return"] do
    let split := body.splitOn terminal
    unless split.length == 2 && (split[0]!.splitOn "(drop (call $pf_storage_write").length ≥ 3 do
      throwError s!"state was not persisted before dual terminal {terminal}"
  logInfo m!"proofforge-near-promise-or-value: digest = {IR.digestHex program}"

#pf_near_promise_or_value_check

end Tests.NearPromiseOrValueSpec
