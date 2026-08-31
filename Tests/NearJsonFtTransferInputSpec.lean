import Examples.NearJsonFtTransferInput
import Lean
import ProofForge

namespace Tests.NearJsonFtTransferInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonFtTransferWhitespace == 32
#guard Codec.maxJsonFtTransferInputBytes == 786
#guard match Codec.targetInputPlan Codec.ftTransferArgsSchema with
  | .ok .jsonFtTransferArgs => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("receiverId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("memo", Codec.optionalMemo16Schema)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtTransferArgs" #[
    ("receiverId", Codec.accountIdSchema), ("amount", .scalar .uint128)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.record "ProofForge.Wasm.Near.Runtime.FtTransferArgs" #[
    ("receiverId", Codec.accountIdSchema), ("amount", .scalar .uint128),
    ("memo", Codec.optionalMemo16Schema), ("extra", .scalar .uint64)]) with
  | .error _ => true | _ => false

elab "#pf_near_json_ft_transfer_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearJsonFtTransferInput with
    | .ok program => pure program | .error reason => throwError reason
  for method in source.methods do
    if method.ixName.startsWith "inspect" || method.ixName == "commitMemoLength" then
      unless method.paramCount == 1 && method.paramSchemas == #[Codec.ftTransferArgsSchema] do
        throwError m!"extractor lost exact FtTransferArgs schema on {method.ixName}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-ft-transfer-args-bounded-v1(max-wire=786,ws=32,order=any,keys=raw,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "inspect" || method.ixName == "commitMemoLength" then
      unless method.inputSchema == some Codec.ftTransferArgsSchema &&
          method.inputPolicy == policy && method.paramCount == 15 do
        throwError s!"target lost combined transfer input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_ft_transfer_args", "(func $pf_json_ft_key",
      "(func $pf_json_account_string", "(func $pf_json_u128_string",
      "(func $pf_json_memo_string", "(i64.const 786)",
      "(call $pf_arena_alloc (i64.const 120) (i64.const 8))",
      "(func (export \"inspectReceiverLength\")", "(func (export \"commitMemoLength\")"] do
    unless wat.contains anchor do throwError s!"combined transfer WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_ft_transfer_args").length == 2 do
    throwError "combined transfer parser must be emitted exactly once"
  if wat.contains "(export \"ft_transfer\")" then
    throwError "parser-only fixture must not export ft_transfer"
  logInfo m!"proofforge-near-json-ft-transfer-input: digest = {IR.digestHex program}"

#pf_near_json_ft_transfer_input_check

end Tests.NearJsonFtTransferInputSpec
