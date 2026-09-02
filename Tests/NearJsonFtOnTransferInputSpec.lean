import Examples.Near.NearJsonFtOnTransferInput
import Lean
import ProofForge

namespace Tests.NearJsonFtOnTransferInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonFtOnTransferWhitespace == 32
#guard Codec.maxJsonFtOnTransferInputBytes == 1071
#guard Codec.InputPlan.localCount .jsonFtOnTransferArgs == 20
#guard match Codec.targetInputPlan Codec.ftOnTransferArgsSchema with
  | .ok .jsonFtOnTransferArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("senderId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("msg", Codec.boundedMessage64Schema)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtOnTransferArgs" #[
    ("senderId", Codec.accountIdSchema), ("amount", .scalar .uint128)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtOnTransferArgs" #[
    ("senderId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("msg", Codec.boundedMessage64Schema), ("extra", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_ft_on_transfer_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonFtOnTransferInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName.startsWith "sender" || method.ixName.startsWith "amount" ||
        method.ixName.startsWith "message" || method.ixName == "commitAmountHigh" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.ftOnTransferArgsSchema] do
        throwError m!"extractor lost exact FtOnTransferArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-ft-on-transfer-args-bounded-v1(max-wire=1071,ws=32,order=any,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "sender" || method.ixName.startsWith "amount" ||
        method.ixName.startsWith "message" || method.ixName == "commitAmountHigh" then
      unless method.inputSchema == some Codec.ftOnTransferArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 20 do
        throwError s!"target lost receiver argument input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_ft_on_transfer_args", "(func $pf_json_ft_on_transfer_key",
      "(func $pf_json_account_string", "(func $pf_json_u128_string", "(func $pf_json_memo_string",
      "(i64.const 1071)", "(call $pf_arena_alloc (i64.const 160) (i64.const 8))",
      "(func (export \"senderLength\")", "(func (export \"messageW7\")",
      "(func (export \"commitAmountHigh\")"] do
    unless wat.contains anchor do throwError s!"receiver argument WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_ft_on_transfer_args").length == 2 do
    throwError "receiver argument parser must be emitted exactly once"
  let senderParts := wat.splitOn "(func (export \"senderLength\")"
  unless senderParts.length == 2 do throwError "missing unique senderLength wrapper"
  let senderBody := (senderParts[1]!).splitOn "(func (export \"" |>.head!
  unless (senderBody.splitOn "(call $pf_input").length == 2 &&
      (senderBody.splitOn "(call $pf_read_register (i64.const 0)").length == 2 &&
      (senderBody.splitOn "(i64.store (i32.add (local.get $pf_ft_on_transfer_args_ptr)").length == 21 &&
      (senderBody.splitOn "(call $pf_json_ft_on_transfer_args").length == 2 do
    throwError "receiver wrapper must input/read once and clear all 20 leaves before one parse"
  if wat.contains "(export \"ft_on_transfer\")" || wat.contains "(import \"env\" \"promise_" then
    throwError "parser-only receiver fixture acquired standard export or Promise behavior"
  logInfo m!"proofforge-near-json-ft-on-transfer-input: digest = {IR.digestHex program}"

#pf_near_json_ft_on_transfer_input_check

end Tests.NearJsonFtOnTransferInputSpec
