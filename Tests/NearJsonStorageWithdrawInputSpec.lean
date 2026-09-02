import Examples.Near.NearJsonStorageWithdrawInput
import Lean
import ProofForge

namespace Tests.NearJsonStorageWithdrawInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonStorageWithdrawWhitespace == 32
#guard Codec.maxJsonStorageWithdrawInputBytes == 279
#guard Codec.storageWithdrawArgsSchema ==
  .record "ProofForge.Wasm.Near.Runtime.StorageWithdrawArgs" #[
    ("amountPresent", .scalar .uint64), ("amount", .scalar .uint128)]
#guard match Codec.targetInputPlan Codec.storageWithdrawArgsSchema with
  | .ok .jsonStorageWithdrawArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("amountPresent", .scalar .uint64), ("amount", .scalar .uint128)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record
    "ProofForge.Wasm.Near.Runtime.StorageWithdrawArgs" #[
      ("amountPresent", .scalar .uint64), ("amount", .scalar .uint128),
      ("extra", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_storage_withdraw_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env
      `Examples.Near.NearJsonStorageWithdrawInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName == "amountPresent" || method.ixName == "amountW0" ||
        method.ixName == "amountW1" || method.ixName == "commitW1" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.storageWithdrawArgsSchema] do
        throwError m!"extractor lost exact StorageWithdrawArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-storage-withdraw-args-bounded-v1(max-wire=279,ws=32,digits=1..39,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName == "amountPresent" || method.ixName == "amountW0" ||
        method.ixName == "amountW1" || method.ixName == "commitW1" then
      unless method.inputSchema == some Codec.storageWithdrawArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 3 do
        throwError s!"target lost storage-withdraw input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_storage_withdraw_args", "(func $pf_json_u128_string",
      "(i64.const 279)", "(call $pf_arena_alloc (i64.const 24) (i64.const 8))",
      "(func (export \"amountPresent\")", "(func (export \"commitW1\")"] do
    unless wat.contains anchor do throwError s!"storage-withdraw parser WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_storage_withdraw_args").length == 2 &&
      (wat.splitOn "(func $pf_json_u128_string").length == 2 do
    throwError "storage-withdraw parser helpers must be emitted exactly once"
  for exportName in #["amountPresent", "amountW0", "amountW1", "commitW1"] do
    let parts := wat.splitOn s!"(func (export \"{exportName}\")"
    unless parts.length == 2 do throwError s!"missing unique {exportName} export"
    let body := (parts[1]!).splitOn "(func (export \"" |>.head!
    let inputRead :=
      "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))"
    unless (body.splitOn "(call $pf_input").length == 2 &&
        (body.splitOn inputRead).length == 2 do
      throwError s!"{exportName} must issue exactly one host input/read pair"
    for offset in #[0, 8, 16] do
      let clear := s!"(i64.store (i32.add (local.get $pf_storage_withdraw_args_ptr) (i32.const {offset})) (i64.const 0))"
      unless body.contains clear do
        throwError s!"{exportName} did not clear frame offset {offset} before parsing"
  if wat.contains "(export \"storage_withdraw\")" then
    throwError "parser-only fixture must not export storage_withdraw"
  logInfo m!"proofforge-near-json-storage-withdraw-input: digest = {IR.digestHex program}"

#pf_near_json_storage_withdraw_input_check

end Tests.NearJsonStorageWithdrawInputSpec
