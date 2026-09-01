import Examples.NearJsonFtTransferCallInput
import Lean
import ProofForge

namespace Tests.NearJsonFtTransferCallInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonFtTransferCallWhitespace == 32
#guard Codec.maxJsonFtTransferCallInputBytes == 1179
#guard match Codec.targetInputPlan Codec.ftTransferCallArgsSchema with
  | .ok .jsonFtTransferCallArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("receiverId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("memo", Codec.optionalMemo16Schema), ("msg", Codec.boundedMessage64Schema)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtTransferCallArgs" #[
    ("receiverId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("memo", Codec.optionalMemo16Schema)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_ft_transfer_call_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env
      `Examples.NearJsonFtTransferCallInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName != "initialize" && method.ixName != "get" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.ftTransferCallArgsSchema] do
        throwError m!"extractor lost exact FtTransferCallArgs schema on {method.ixName}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-ft-transfer-call-args-bounded-v1(max-wire=1179,ws=32,order=any,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName != "get" then
      unless method.inputSchema == some Codec.ftTransferCallArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 24 do
        throwError s!"target lost transfer-call input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_ft_transfer_call_args",
      "(func $pf_json_ft_transfer_call_key", "(func $pf_json_account_string",
      "(func $pf_json_u128_string", "(func $pf_json_memo_string", "(i64.const 1179)",
      "(call $pf_arena_alloc (i64.const 192) (i64.const 8))",
      "(func (export \"messageW7\")", "(func (export \"commitMessageLength\")"] do
    unless wat.contains anchor do throwError s!"transfer-call parser WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_ft_transfer_call_args").length == 2 &&
      (wat.splitOn "(call $pf_input").length == program.entries.size + 2 do
    throwError "transfer-call parser/helper or one-input-read wrapper multiplicity changed"
  if wat.contains "(export \"ft_transfer_call\")" || wat.contains "promise_batch" then
    throwError "parser-only fixture gained standard export or Promise effects"
  logInfo m!"proofforge-near-json-ft-transfer-call-input: digest = {IR.digestHex program}"

#pf_near_json_ft_transfer_call_input_check

end Tests.NearJsonFtTransferCallInputSpec
