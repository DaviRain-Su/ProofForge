import Examples.NearOutput
import Lean
import ProofForge

/-! Canonical Borsh bounded-output planning and WAT checks. -/

namespace Tests.NearOutputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard match Codec.outputPlan (.boundedBytes 8) with
  | .ok plan => plan == { kind := .bytes, capacity := 8, elementWidth := 1, validateUtf8 := false }
  | .error _ => false
#guard match Codec.outputPlan (.boundedString 8) with
  | .ok plan => plan == { kind := .string, capacity := 8, elementWidth := 1, validateUtf8 := true }
  | .error _ => false
#guard match Codec.outputPlan (.boundedArray 4 (.scalar .uint16)) with
  | .ok plan => plan == { kind := .array, capacity := 4, elementWidth := 2, validateUtf8 := false }
  | .error _ => false
#guard match Codec.outputPlan (.boundedBytes 65) with | .error _ => true | .ok _ => false
#guard match Codec.outputPlan (.boundedArray 4 (.scalar .boolean)) with
  | .error _ => true
  | .ok _ => false
#guard match Codec.targetOutputPlan (.scalar .uint128) with
  | .ok .jsonU128 => true
  | _ => false
#guard match Codec.targetOutputPlan (.record "Pair" #[
    ("w0", .scalar .uint64), ("w1", .scalar .uint64)]) with
  | .error _ => true
  | .ok _ => false
#guard match Codec.targetOutputPlan (.record "OtherHash" #[
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64)]) with
  | .error _ => true
  | .ok _ => false

private def returnCount (method : IR.Method) : Nat :=
  method.ops.foldl (init := 0) fun count op =>
    match op with
    | .returnU64 _ => count + 1
    | _ => count

elab "#pf_near_output_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearOutput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceBytes := source.methods.find? (·.ixName == "staticBytes")
    | throwError "missing source staticBytes"
  let some sourceValues := source.methods.find? (·.ixName == "staticValues")
    | throwError "missing source staticValues"
  let some sourceJson := source.methods.find? (·.ixName == "jsonU128Asymmetric")
    | throwError "missing source jsonU128Asymmetric"
  let some sourceHash := source.methods.find? (·.ixName == "jsonBase64Hash32")
    | throwError "missing source jsonBase64Hash32"
  unless sourceBytes.retSchema == .boundedBytes 8 && sourceBytes.retCount == 9 &&
      sourceValues.retSchema == .boundedArray 4 (.scalar .uint16) &&
      sourceValues.retCount == 5 && sourceJson.retSchema == .scalar .uint128 &&
      sourceJson.retCount == 2 && sourceJson.ops.size == 2 &&
      sourceHash.retSchema == Codec.base64Hash32ResultSchema && sourceHash.retCount == 4 &&
      (match sourceJson.ops[0]!, sourceJson.ops[1]! with
        | .returnU64 (.lit 2), .returnU64 (.lit 1) => true
        | _, _ => false) do
    throwError "extractor did not retain bounded output schemas/frames"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some bytes := program.entries.find? (·.ixName == "staticBytes")
    | throwError "missing target staticBytes"
  let some string := program.entries.find? (·.ixName == "staticString")
    | throwError "missing target staticString"
  let some values := program.entries.find? (·.ixName == "staticValues")
    | throwError "missing target staticValues"
  let some echo := program.entries.find? (·.ixName == "echoBytes")
    | throwError "missing target echoBytes"
  let some json := program.entries.find? (·.ixName == "jsonU128Asymmetric")
    | throwError "missing target jsonU128Asymmetric"
  let some hash := program.entries.find? (·.ixName == "jsonBase64Hash32")
    | throwError "missing target jsonBase64Hash32"
  unless bytes.outputSchema == some (.boundedBytes 8) &&
      bytes.outputPolicy == "near-borsh-output-bytes-v1(capacity=8,width=1)" &&
      bytes.tupleArity == some 9 && returnCount bytes == 9 &&
      string.outputSchema == some (.boundedString 8) && string.tupleArity == some 9 &&
      values.outputSchema == some (.boundedArray 4 (.scalar .uint16)) &&
      values.tupleArity == some 5 && returnCount values == 5 &&
      echo.inputSchema == some (.boundedBytes 8) &&
      echo.outputSchema == some (.boundedBytes 8) &&
      json.outputSchema == some (.scalar .uint128) &&
      json.outputPolicy == "near-json-u128-string-v1" && json.tupleArity == some 2 &&
      hash.outputSchema == some Codec.base64Hash32ResultSchema &&
      hash.outputPolicy == "near-json-base64-hash32-v1" && hash.tupleArity == some 4 &&
      returnCount json == 2 do
    throwError "NEAR target lost bounded output metadata or fixed return leaves"
  let malformedCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "staticBytes" then { method with retCount := 8 } else method }
  match IR.fromExtracted malformedCount with
  | .error reason =>
      unless reason.contains "output frame does not match" do
        throwError s!"wrong malformed output-frame rejection: {reason}"
  | .ok _ => throwError "malformed bounded output frame was accepted"
  let malformedJsonCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "jsonU128Asymmetric" then { method with retCount := 1 } else method }
  match IR.fromExtracted malformedJsonCount with
  | .error reason =>
      unless reason.contains "output frame does not match its JSON u128 plan" do
        throwError s!"wrong malformed JSON u128 frame rejection: {reason}"
  | .ok _ => throwError "malformed JSON u128 output frame was accepted"
  let mutatingHash := { source with methods := source.methods.map fun method =>
    if method.ixName == "jsonBase64Hash32" then { method with kind := .increment } else method }
  match IR.fromExtracted mutatingHash with
  | .error reason =>
      unless reason.contains "Base64 hash output currently requires a view" do
        throwError s!"wrong mutating Base64 hash rejection: {reason}"
  | .ok _ => throwError "mutating Base64 hash output was accepted"
  let mutatingOutput := { source with methods := source.methods.map fun method =>
    if method.ixName == "staticBytes" then { method with kind := .increment } else method }
  match IR.fromExtracted mutatingOutput with
  | .error reason =>
      unless reason.contains "bounded output currently requires a view" do
        throwError s!"wrong mutating bounded-output rejection: {reason}"
  | .ok _ => throwError "mutating bounded output was accepted"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(local $pf_output_ptr i32)",
    "(local $pf_output_length i64)",
    "(call $pf_arena_alloc (i64.const 12) (i64.const 8))",
    "i32.store (local.get $pf_output_ptr)",
    "i64.store8 (i32.add (local.get $pf_output_ptr)",
    "i64.store16 (i32.add (local.get $pf_output_ptr)",
    "(if (i64.gt_u (local.get $pf_output_length) (i64.const 8))",
    "(if (i64.gt_u (i64.const 65535) (i64.const 65535))",
    "(call $pf_utf8_valid (i32.add (local.get $pf_output_ptr) (i32.const 4))",
    "(call $pf_value_return (i64.add (i64.const 4)",
    "(i64.extend_i32_u (local.get $pf_output_ptr))",
    "(func $pf_u128_decimal",
    "(call $pf_arena_alloc (i64.const 41) (i64.const 1))",
    "(call $pf_arena_alloc (i64.const 39) (i64.const 1))",
    "(i64.store8 (local.get $pf_output_ptr) (i64.const 34))",
    "(local.set $pf_output_length (call $pf_u128_decimal",
    "(i64.add (local.get $pf_output_length) (i64.const 2))",
    "(call $pf_arena_alloc (i64.const 46) (i64.const 1))",
    "(i32.const 44)) (i64.const 61))",
    "(call $pf_value_return (i64.const 46)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR bounded-output WAT missing {anchor}"
  if wat.contains "(func $pf_json_escape_byte" then
    throwError "pure JSON u128 output pulled in the unrelated JSON string escaper"
  unless (wat.splitOn "(func $pf_u128_decimal").length == 2 do
    throwError "JSON u128 output did not include exactly one shared decimal helper"
  let hashParts := wat.splitOn "(func (export \"jsonBase64Hash32\")"
  unless hashParts.length == 2 do
    throwError "missing unique JSON Base64 hash export body"
  let hashBody := (hashParts[1]!).splitOn "(func (export \"" |>.head!
  unless (hashBody.splitOn "(call $pf_value_return").length == 2 &&
      hashBody.contains "(i64.const 43)" && hashBody.contains "(i64.const 47)" do
    throwError "Base64 hash export lost one return or STANDARD alphabet branches"
  let jsonParts := wat.splitOn "(func (export \"jsonU128Asymmetric\")"
  unless jsonParts.length == 2 do
    throwError "missing unique JSON u128 export body"
  let jsonBody := (jsonParts[1]!).splitOn "(func (export \"" |>.head!
  unless (jsonBody.splitOn "(call $pf_value_return").length == 2 do
    throwError "JSON u128 export must issue exactly one value_return"
  let mismatchedPolicy := { program with entries := program.entries.map fun method =>
    if method.ixName == "staticBytes" then { method with outputPolicy := "wrong" } else method }
  match Emit.emit mismatchedPolicy with
  | .error reason =>
      unless reason.contains "output policy does not match" do
        throwError s!"wrong output-policy rejection: {reason}"
  | .ok _ => throwError "mismatched output policy was accepted"
  logInfo m!"proofforge-near-output: digest = {IR.digestHex program}"

#pf_near_output_check

end Tests.NearOutputSpec
