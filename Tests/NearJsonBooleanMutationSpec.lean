import Examples.NearJsonBooleanMutation
import Examples.NearPromise
import Lean
import ProofForge

namespace Tests.NearJsonBooleanMutationSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard match Codec.targetOutputPlan Codec.jsonBooleanResultSchema with
  | .ok .jsonBoolean => true | _ => false
#guard match Codec.targetOutputPlan (.record "Ordinary" #[("value", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_boolean_mutation_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env
      `Examples.NearJsonBooleanMutation with
    | .ok program => pure program | .error reason => throwError reason
  let some extracted := source.methods.find? (·.ixName == "setChecked")
    | throwError "missing setChecked"
  unless extracted.kind == .increment && extracted.retCount == 1 &&
      extracted.retSchema == Codec.jsonBooleanResultSchema do
    throwError m!"extractor lost exact JsonBooleanResult schema: {repr extracted.retSchema}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let some target := program.entries.find? (·.ixName == "setChecked")
    | throwError "missing target setChecked"
  unless target.kind == .increment && target.outputSchema == some Codec.jsonBooleanResultSchema &&
      target.outputPolicy == "near-json-boolean-v1" && target.tupleArity == some 1 do
    throwError "target lost mutating JSON Boolean output policy"
  let viewSource := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setChecked" then { candidate with kind := .get } else candidate }
  match IR.fromExtracted viewSource with
  | .error reason =>
      unless reason.contains "JSON Boolean output requires a mutating entry" do
        throwError s!"wrong JSON Boolean view rejection: {reason}"
  | .ok _ => throwError "JSON Boolean output was accepted on a view"
  let malformed := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setChecked" then { candidate with retCount := 2 } else candidate }
  match IR.fromExtracted malformed with
  | .error reason =>
      unless reason.contains "output frame does not match its JSON Boolean plan" do
        throwError s!"wrong malformed JSON Boolean rejection: {reason}"
  | .ok _ => throwError "malformed JSON Boolean frame was accepted"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  let parts := wat.splitOn "(func (export \"setChecked\")"
  unless parts.length == 2 do throwError "missing unique setChecked export"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  for anchor in #["(call $pf_arena_alloc (i64.const 5) (i64.const 1))",
      "(i32.const 1936482662)", "(i32.const 1702195828)",
      "(call $pf_value_return (local.get $pf_output_length)"] do
    unless body.contains anchor do throwError s!"JSON Boolean WAT missing {anchor}"
  unless (body.splitOn "(call $pf_storage_write").length == 3 &&
      (body.splitOn "(call $pf_value_return").length == 2 do
    throwError "JSON Boolean mutation must store two state fields before one value_return"
  let beforeReturn := (body.splitOn "(call $pf_value_return").head!
  unless (beforeReturn.splitOn "(call $pf_storage_write").length == 3 do
    throwError "JSON Boolean return precedes state persistence"
  let promiseSource ← match ProofForge.Extract.extractModuleIR env `Examples.NearPromise with
    | .ok program => pure program | .error reason => throwError reason
  let promiseMethods := promiseSource.methods.map fun candidate =>
    if candidate.ixName == "transferCallerReturned" then
      { candidate with retSchema := Codec.jsonBooleanResultSchema, retCount := 1 }
    else candidate
  let promiseProgram ← match IR.fromExtracted { promiseSource with methods := promiseMethods } with
    | .ok program => pure program | .error reason => throwError reason
  match Emit.emit promiseProgram with
  | .error reason =>
      unless reason.contains "JSON Boolean output cannot also return a promise" do
        throwError s!"wrong JSON Boolean/Promise rejection: {reason}"
  | .ok _ => throwError "JSON Boolean output was incorrectly combined with promise_return"
  logInfo m!"proofforge-near-json-boolean-mutation: digest = {IR.digestHex program}"

#pf_near_json_boolean_mutation_check

end Tests.NearJsonBooleanMutationSpec
