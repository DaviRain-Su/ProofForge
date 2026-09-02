import Examples.Near.NearJsonStorageUnregisterInput
import Lean
import ProofForge

namespace Tests.NearJsonStorageUnregisterInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonStorageUnregisterWhitespace == 32
#guard Codec.maxJsonStorageUnregisterInputBytes == 47
#guard match Codec.targetInputPlan Codec.storageUnregisterArgsSchema with
  | .ok .jsonStorageUnregisterArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[("force", .scalar .uint64)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record
    "ProofForge.Wasm.Near.Runtime.StorageUnregisterArgs" #[
      ("force", .scalar .uint64), ("extra", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_storage_unregister_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env
      `Examples.Near.NearJsonStorageUnregisterInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName == "inspectForce" || method.ixName == "commitForce" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.storageUnregisterArgsSchema] do
        throwError m!"extractor lost exact StorageUnregisterArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-storage-unregister-args-bounded-v1(max-wire=47,ws=32,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName == "inspectForce" || method.ixName == "commitForce" then
      unless method.inputSchema == some Codec.storageUnregisterArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 1 do
        throwError s!"target lost storage-unregister input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_storage_unregister_args", "(i64.const 47)",
      "(call $pf_arena_alloc (i64.const 8) (i64.const 8))",
      "(func (export \"inspectForce\")", "(func (export \"commitForce\")"] do
    unless wat.contains anchor do throwError s!"storage-unregister parser WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_storage_unregister_args").length == 2 do
    throwError "storage-unregister parser must be emitted exactly once"
  if wat.contains "(export \"storage_unregister\")" then
    throwError "parser-only fixture must not export storage_unregister"
  logInfo m!"proofforge-near-json-storage-unregister-input: digest = {IR.digestHex program}"

#pf_near_json_storage_unregister_input_check

end Tests.NearJsonStorageUnregisterInputSpec
