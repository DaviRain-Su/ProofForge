import Examples.Near.NearJsonMemoInput
import Lean
import ProofForge

namespace Tests.NearJsonMemoInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonMemoWhitespace == 32
#guard Codec.maxJsonMemoInputBytes == 139
#guard match Codec.targetInputPlan Codec.optionalMemo16Schema with
  | .ok .jsonOptionalMemo16 => true | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("present", .scalar .uint64), ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64)]) with
  | .error _ => true | _ => false
#guard match Codec.targetInputPlan (.option (.boundedString 16)) with
  | .error _ => true | _ => false

elab "#pf_near_json_memo_input_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonMemoInput with
    | .ok program => pure program | .error reason => throwError reason
  for name in #["memoPresent", "memoLength", "memoW0", "memoW1", "commitLength"] do
    let some method := source.methods.find? (·.ixName == name) | throwError s!"missing {name}"
    unless method.paramCount == 1 && method.paramSchemas == #[Codec.optionalMemo16Schema] do
      throwError m!"extractor lost OptionalMemo16 schema on {name}: {repr method.paramSchemas}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let policy :=
    "near-json-optional-memo16-object-canonical-v1(max-wire=139,ws=32,decoded-bytes=0..16,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "memo" || method.ixName == "commitLength" then
      unless method.inputSchema == some Codec.optionalMemo16Schema &&
          method.inputPolicy == policy && method.paramCount == 4 do
        throwError s!"target lost optional memo input on {method.ixName}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func $pf_json_optional_memo16", "(func $pf_json_memo_string",
      "(func $pf_json_memo_put_cp", "(func $pf_utf8_valid", "(i64.const 139)",
      "(call $pf_arena_alloc (i64.const 32) (i64.const 8))",
      "(func (export \"memoPresent\")", "(func (export \"commitLength\")"] do
    unless wat.contains anchor do throwError s!"optional memo WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_optional_memo16").length == 2 &&
      (wat.splitOn "(func $pf_json_memo_string").length == 2 do
    throwError "optional memo helpers must be emitted exactly once"
  logInfo m!"proofforge-near-json-memo-input: digest = {IR.digestHex program}"

#pf_near_json_memo_input_check

end Tests.NearJsonMemoInputSpec
