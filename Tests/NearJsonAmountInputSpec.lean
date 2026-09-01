import Examples.NearJsonAmountInput
import Lean
import ProofForge

/-! Canonical one-field quoted-u128 amount JSON object input invariants. -/

namespace Tests.NearJsonAmountInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonU128Whitespace == 32
#guard Codec.maxJsonU128InputBytes == 279
#guard match Codec.targetInputPlan (.scalar .uint128) with
  | .ok .jsonU128Amount => true
  | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("w0", .scalar .uint64), ("w1", .scalar .uint64)]) with
  | .error _ => true
  | .ok _ => false

elab "#pf_near_json_amount_input_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearJsonAmountInput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceW0 := source.methods.find? (·.ixName == "amountW0")
    | throwError "missing source amountW0"
  let some sourceW1 := source.methods.find? (·.ixName == "amountW1")
    | throwError "missing source amountW1"
  let some sourceCommit := source.methods.find? (·.ixName == "commitW1")
    | throwError "missing source commitW1"
  unless sourceW0.paramCount == 1 && sourceW0.paramSchemas == #[.scalar .uint128] &&
      sourceW1.paramSchemas == #[.scalar .uint128] &&
      sourceCommit.paramSchemas == #[.scalar .uint128] do
    throwError m!"extractor lost exact UInt128 input schema: {repr sourceW0.paramSchemas}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let policy :=
    "near-json-u128-amount-object-canonical-v1(max-wire=279,ws=32,digits=1..39,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "amount" || method.ixName == "commitW1" then
      unless method.inputSchema == some (.scalar .uint128) && method.inputPolicy == policy &&
          method.paramCount == 2 do
        throwError s!"target lost quoted-u128 input plan for {method.ixName}"
  let multiple := { source with methods := source.methods.map fun method =>
    if method.ixName == "amountW0" then
      { method with paramCount := 2, paramSchemas := #[.scalar .uint128, .scalar .uint64] }
    else method }
  match IR.fromExtracted multiple with
  | .error reason =>
      unless reason.contains "wants UInt64 scalar parameters" ||
          reason.contains "exactly one specialized input parameter" do
        throwError s!"wrong multiple-parameter quoted-u128 rejection: {reason}"
  | .ok _ => throwError "multiple-parameter quoted-u128 input was accepted"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func $pf_json_u128_amount",
    "(func $pf_json_u128_string",
    "(func $pf_json_amount_hex",
    "(i64.const 279)",
    "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
    "(call $pf_input (i64.const 0))",
    "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))",
    "(call $pf_json_u128_amount (local.get $pf_input_ptr)",
    "(i64.load (local.get $pf_u128_ptr))",
    "(i64.load (i32.add (local.get $pf_u128_ptr) (i32.const 8)))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR JSON amount WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_u128_amount").length == 2 &&
      (wat.splitOn "(func $pf_json_u128_string").length == 2 do
    throwError "JSON amount parser helpers must be emitted exactly once"
  for exportName in #["amountW0", "amountW1", "commitW1"] do
    let parts := wat.splitOn s!"(func (export \"{exportName}\")"
    unless parts.length == 2 do throwError s!"missing unique {exportName} export"
    let body := (parts[1]!).splitOn "(func (export \"" |>.head!
    let inputRead :=
      "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))"
    unless (body.splitOn "(call $pf_input").length == 2 &&
        (body.splitOn inputRead).length == 2 do
      throwError s!"{exportName} must issue exactly one host input/read pair"
  logInfo m!"proofforge-near-json-amount-input: digest = {IR.digestHex program}"

#pf_near_json_amount_input_check

end Tests.NearJsonAmountInputSpec
