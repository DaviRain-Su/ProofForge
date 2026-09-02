import Examples.Near.NearJsonAccountInput
import Lean
import ProofForge

/-! Bounded one-field AccountId JSON object input extraction and WAT invariants. -/

namespace Tests.NearJsonAccountInputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonAccountWhitespace == 32
#guard Codec.maxJsonAccountInputBytes == 433
#guard match Codec.targetInputPlan Codec.accountIdSchema with
  | .ok .jsonAccountId => true
  | _ => false
#guard match Codec.targetInputPlan (.record "Ordinary" #[
    ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64),
    ("w4", .scalar .uint64), ("w5", .scalar .uint64),
    ("w6", .scalar .uint64), ("w7", .scalar .uint64)]) with
  | .error _ => true
  | .ok _ => false

elab "#pf_near_json_account_input_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonAccountInput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceLength := source.methods.find? (·.ixName == "accountLength")
    | throwError "missing source accountLength"
  let some sourceW7 := source.methods.find? (·.ixName == "accountW7")
    | throwError "missing source accountW7"
  let some sourceTouch := source.methods.find? (·.ixName == "touch")
    | throwError "missing source touch"
  unless sourceLength.paramCount == 1 && sourceLength.paramSchemas == #[Codec.accountIdSchema] &&
      sourceW7.paramSchemas == #[Codec.accountIdSchema] do
    throwError m!"extractor lost exact AccountId input schema: {repr sourceLength.paramSchemas}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let policy :=
    "near-json-account-id-object-bounded-v1(max-wire=433,ws=32,keys=canonical,unknown=reject)"
  for method in program.entries do
    if method.ixName.startsWith "account" then
      unless method.inputSchema == some Codec.accountIdSchema && method.inputPolicy == policy &&
          method.paramCount == 9 do
        throwError s!"target lost AccountId input plan for {method.ixName}"
  let mutatingMethod := { sourceTouch with
    ixName := "accountMutating", paramCount := 1, paramSchemas := #[Codec.accountIdSchema] }
  let mutating := { source with methods := #[mutatingMethod] }
  match IR.fromExtracted mutating with
  | .error reason =>
      unless reason.contains "JSON AccountId input currently requires a view" do
        throwError s!"wrong mutating AccountId-input rejection: {reason}"
  | .ok _ => throwError "mutating JSON AccountId input was accepted"
  let multiple := { source with methods := source.methods.map fun method =>
    if method.ixName == "accountLength" then
      { method with paramCount := 2, paramSchemas := #[Codec.accountIdSchema, .scalar .uint64] }
    else method }
  match IR.fromExtracted multiple with
  | .error reason =>
      unless reason.contains "exactly one specialized input parameter" do
        throwError s!"wrong multiple-parameter AccountId rejection: {reason}"
  | .ok _ => throwError "multiple-parameter JSON AccountId input was accepted"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func $pf_json_account_id",
    "(func $pf_json_account_key",
    "(func $pf_json_account_hex",
    "(i64.const 433)",
    "(i32.const 64)",
    "(i32.const 32)",
    "(call $pf_input (i64.const 0))",
    "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))",
    "(call $pf_json_account_id (local.get $pf_input_ptr)",
    "(local.set $pf_p8",
    "(call $pf_panic_utf8 (i64.const 5)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR JSON AccountId WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_account_id").length == 2 do
    throwError "JSON AccountId parser helper must be emitted exactly once"
  let parts := wat.splitOn "(func (export \"accountLength\")"
  unless parts.length == 2 do throwError "missing unique accountLength export"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  let inputRead :=
    "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))"
  unless (body.splitOn "(call $pf_input").length == 2 &&
      (body.splitOn inputRead).length == 2 do
    throwError s!"JSON AccountId entry must issue exactly one host input/read pair: " ++
      s!"input={(body.splitOn "(call $pf_input").length}, " ++
      s!"read={(body.splitOn inputRead).length}"
  logInfo m!"proofforge-near-json-account-input: digest = {IR.digestHex program}"

#pf_near_json_account_input_check

end Tests.NearJsonAccountInputSpec
