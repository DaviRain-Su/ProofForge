import Examples.NearJsonMessageInput
import Lean
import ProofForge

namespace Tests.NearJsonMessageInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonMessageWhitespace == 32
#guard Codec.maxJsonMessageInputBytes == 426
#guard match Codec.targetInputPlan Codec.boundedMessage64Schema with
  | .ok .jsonMessage64 => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64),
    ("w4", .scalar .uint64), ("w5", .scalar .uint64),
    ("w6", .scalar .uint64), ("w7", .scalar .uint64)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.boundedString 64) with
  | .ok (.borsh _) => true | _ => false

elab "#pf_near_json_message_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearJsonMessageInput with
    | .ok program => pure program | .error reason => throwError reason
  for name in #["messageLength", "messageW0", "messageW1", "messageW2", "messageW3",
      "messageW4", "messageW5", "messageW6", "messageW7", "commitLength"] do
    let some method := source.methods.find? (·.ixName == name) | throwError s!"missing {name}"
    unless method.paramCount == 1 && method.paramSchemas == #[Codec.boundedMessage64Schema] do
      throwError m!"extractor lost BoundedMessage64 schema on {name}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-message64-object-canonical-v1(max-wire=426,ws=32,decoded-bytes=0..64,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "message" || method.ixName == "commitLength" then
      unless method.inputSchema == some Codec.boundedMessage64Schema &&
          method.inputPolicy == policy && method.paramCount == 9 do
        throwError s!"target lost bounded message input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_message64", "(func $pf_json_memo_string",
      "(func $pf_json_memo_put_cp", "(func $pf_utf8_valid", "(i64.const 426)",
      "(call $pf_arena_alloc (i64.const 72) (i64.const 8))",
      "(param $cap i32)", "(loop $chars", "(func (export \"messageLength\")",
      "(func (export \"commitLength\")"] do
    unless wat.contains anchor do throwError s!"bounded message WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_message64").length == 2 &&
      (wat.splitOn "(func $pf_json_memo_string").length == 2 &&
      (wat.splitOn "(call $pf_json_message64").length == 11 do
    throwError "message helpers must be unique and each message wrapper must parse once"
  if wat.contains "ft_transfer_call" || wat.contains "promise_batch" then
    throwError "message codec fixture must not expose transfer-call or Promise behavior"
  logInfo m!"proofforge-near-json-message-input: digest = {IR.digestHex program}"

#pf_near_json_message_input_check

end Tests.NearJsonMessageInputSpec
