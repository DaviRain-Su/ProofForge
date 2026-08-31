import Examples.NearJsonStorageDepositInput
import Lean
import ProofForge

namespace Tests.NearJsonStorageDepositInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonStorageDepositWhitespace == 32
#guard Codec.maxJsonStorageDepositInputBytes == 459
#guard match Codec.targetInputPlan Codec.storageDepositArgsSchema with
  | .ok .jsonStorageDepositArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("accountPresent", .scalar .uint64), ("accountId", Codec.accountIdSchema),
    ("registrationOnly", .scalar .uint64)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.StorageDepositArgs" #[
    ("accountId", Codec.accountIdSchema), ("registrationOnly", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_storage_deposit_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearJsonStorageDepositInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName.startsWith "inspect" || method.ixName == "commitRegistrationOnly" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.storageDepositArgsSchema] do
        throwError m!"extractor lost exact StorageDepositArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-storage-deposit-args-bounded-v1(max-wire=459,ws=32,order=any,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "inspect" || method.ixName == "commitRegistrationOnly" then
      unless method.inputSchema == some Codec.storageDepositArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 11 do
        throwError s!"target lost storage-deposit input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_storage_deposit_args", "(func $pf_json_storage_deposit_key",
      "(func $pf_json_account_string", "(i64.const 459)",
      "(call $pf_arena_alloc (i64.const 88) (i64.const 8))",
      "(func (export \"inspectAccountPresent\")",
      "(func (export \"commitRegistrationOnly\")"] do
    unless wat.contains anchor do throwError s!"storage-deposit parser WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_storage_deposit_args").length == 2 &&
      (wat.splitOn "(func $pf_json_account_string").length == 2 do
    throwError "storage-deposit and shared account parsers must each be emitted exactly once"
  if wat.contains "(export \"storage_deposit\")" then
    throwError "parser-only fixture must not export storage_deposit"
  logInfo m!"proofforge-near-json-storage-deposit-input: digest = {IR.digestHex program}"

#pf_near_json_storage_deposit_input_check

end Tests.NearJsonStorageDepositInputSpec
