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
  unless sourceBytes.retSchema == .boundedBytes 8 && sourceBytes.retCount == 9 &&
      sourceValues.retSchema == .boundedArray 4 (.scalar .uint16) &&
      sourceValues.retCount == 5 do
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
  unless bytes.outputSchema == some (.boundedBytes 8) &&
      bytes.outputPolicy == "near-borsh-output-bytes-v1(capacity=8,width=1)" &&
      bytes.tupleArity == some 9 && returnCount bytes == 9 &&
      string.outputSchema == some (.boundedString 8) && string.tupleArity == some 9 &&
      values.outputSchema == some (.boundedArray 4 (.scalar .uint16)) &&
      values.tupleArity == some 5 && returnCount values == 5 &&
      echo.inputSchema == some (.boundedBytes 8) &&
      echo.outputSchema == some (.boundedBytes 8) do
    throwError "NEAR target lost bounded output metadata or fixed return leaves"
  let malformedCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "staticBytes" then { method with retCount := 8 } else method }
  match IR.fromExtracted malformedCount with
  | .error reason =>
      unless reason.contains "output frame does not match" do
        throwError s!"wrong malformed output-frame rejection: {reason}"
  | .ok _ => throwError "malformed bounded output frame was accepted"
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
    "(i64.extend_i32_u (local.get $pf_output_ptr))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR bounded-output WAT missing {anchor}"
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
