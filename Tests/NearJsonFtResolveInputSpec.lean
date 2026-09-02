import Examples.Near.NearJsonFtResolveInput
import Lean
import ProofForge

namespace Tests.NearJsonFtResolveInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonFtResolveWhitespace == 32
#guard Codec.maxJsonFtResolveInputBytes == 1079
#guard Codec.InputPlan.localCount .jsonFtResolveTransferArgs == 20
#guard match Codec.targetInputPlan Codec.ftResolveTransferArgsSchema with
  | .ok .jsonFtResolveTransferArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("senderId", Codec.accountIdSchema), ("receiverId", Codec.accountIdSchema),
    ("amount", .scalar .uint128)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtResolveTransferArgs" #[
    ("senderId", Codec.accountIdSchema), ("receiverId", Codec.accountIdSchema)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtResolveTransferArgs" #[
    ("senderId", Codec.accountIdSchema), ("receiverId", Codec.accountIdSchema),
    ("amount", .scalar .uint128), ("extra", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_ft_resolve_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonFtResolveInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName.startsWith "sender" || method.ixName.startsWith "receiver" ||
        method.ixName.startsWith "amount" || method.ixName == "commitAmountHigh" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.ftResolveTransferArgsSchema] do
        throwError m!"extractor lost exact FtResolveTransferArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-ft-resolve-args-bounded-v1(max-wire=1079,ws=32,order=any,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "sender" || method.ixName.startsWith "receiver" ||
        method.ixName.startsWith "amount" || method.ixName == "commitAmountHigh" then
      unless method.inputSchema == some Codec.ftResolveTransferArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 20 do
        throwError s!"target lost resolver argument input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_ft_resolve_args", "(func $pf_json_ft_resolve_key",
      "(func $pf_json_account_string", "(func $pf_json_u128_string", "(i64.const 1079)",
      "(call $pf_arena_alloc (i64.const 160) (i64.const 8))",
      "(func (export \"senderLength\")", "(func (export \"commitAmountHigh\")"] do
    unless wat.contains anchor do throwError s!"resolver argument WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_ft_resolve_args").length == 2 do
    throwError "resolver argument parser must be emitted exactly once"
  let senderParts := wat.splitOn "(func (export \"senderLength\")"
  unless senderParts.length == 2 do throwError "missing unique senderLength wrapper"
  let senderBody := (senderParts[1]!).splitOn "(func (export \"" |>.head!
  unless (senderBody.splitOn "(call $pf_input").length == 2 &&
      (senderBody.splitOn "(call $pf_read_register (i64.const 0)").length == 2 &&
      (senderBody.splitOn "(i64.store (i32.add (local.get $pf_ft_resolve_args_ptr)").length == 21 &&
      (senderBody.splitOn "(call $pf_json_ft_resolve_args").length == 2 do
    throwError "resolver wrapper must input/read once and clear all 20 leaves before one parse"
  if wat.contains "(export \"ft_resolve_transfer\")" ||
      wat.contains "(import \"env\" \"promise_result\"" then
    throwError "parser-only resolver fixture acquired standard export or Promise-result behavior"
  logInfo m!"proofforge-near-json-ft-resolve-input: digest = {IR.digestHex program}"

#pf_near_json_ft_resolve_input_check

end Tests.NearJsonFtResolveInputSpec
