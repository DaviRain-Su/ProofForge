import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.NearBytes

/-!
# NEAR canonical Borsh bounded bytes/string input

The extractor keeps the logical bounded carrier. The NEAR boundary owns its fixed nine-scalar
frame and exact Borsh decoder; `BoundedString` additionally receives strict Unicode-scalar UTF-8
validation before source operations execute.
-/

open ProofForge
open Lean Elab Command

private def isExpectedBoundedOps (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  match method.ops with
  | #[.returnU64 (.addU64 (.addU64 (.arg 0) (.arg 1)) (.arg 8))] => true
  | _ => false

elab "#pf_guard_near_borsh_inputs" : command => do
  let env ← getEnv
  let extracted ←
    match Extract.extractModuleIR env `Examples.NearBytes none with
    | .ok source => pure source
    | .error reason => throwError reason
  let some rawBytes := extracted.methods.find? (·.ixName == "inspectBytes")
    | throwError "missing extracted inspectBytes"
  let some rawString := extracted.methods.find? (·.ixName == "inspectString")
    | throwError "missing extracted inspectString"
  unless rawBytes.paramCount == 1 && rawBytes.paramSchemas == #[.boundedBytes 8] &&
      rawString.paramCount == 1 && rawString.paramSchemas == #[.boundedString 8] do
    throwError s!"extractor lost bounded input schemas: {repr rawBytes.paramSchemas}, " ++
      s!"{repr rawString.paramSchemas}"
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted extracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let some bytes := program.entries.find? (·.ixName == "inspectBytes")
    | throwError "missing lowered inspectBytes"
  let some text := program.entries.find? (·.ixName == "inspectString")
    | throwError "missing lowered inspectString"
  unless bytes.paramCount == 9 && bytes.inputSchema == some (.boundedBytes 8) &&
      bytes.inputPolicy == "near-borsh-bytes-v1(capacity=8)" &&
      text.paramCount == 9 && text.inputSchema == some (.boundedString 8) &&
      text.inputPolicy == "near-borsh-string-v1(capacity=8)" &&
      isExpectedBoundedOps bytes && isExpectedBoundedOps text do
    throwError "wrong NEAR bounded scalar frame, policy, or rewritten operations"
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok source => pure source
    | .error reason => throwError reason
  let anchors : Array String := #[
    "(func $pf_utf8_valid (param $ptr i32) (param $len i32) (result i32)",
    "(local.set $pf_input_size (call $pf_register_len (i64.const 0)) )",
    "(if (i64.lt_u (local.get $pf_input_size) (i64.const 4))",
    "(if (i64.gt_u (local.get $pf_input_size) (i64.const 12))",
    "(call $pf_read_register (i64.const 0) (i64.const 256))",
    "(local.set $pf_p0 (i64.load32_u (i32.const 256)) )",
    "(if (i64.gt_u (local.get $pf_p0) (i64.const 8))",
    "(if (i64.ne (local.get $pf_input_size) (i64.add (i64.const 4) (local.get $pf_p0)))",
    "(call $pf_utf8_valid (i32.const 260) (i32.wrap_i64 (local.get $pf_p0)))",
    "(local.set $pf_p8 (if (result i64) (i64.lt_u (i64.const 7) (local.get $pf_p0))",
    "(i64.load8_u (i32.const 267))) (else (i64.const 0))))",
    "(i32.const 194)",
    "(i32.const 237)",
    "(i32.const 244)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR bounded-input WAT is missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-bytes-test: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_borsh_inputs
#pf_near_build Examples.NearBytes

#guard
  match ProofForge.Wasm.Near.Codec.inputPlan (.boundedBytes 0) with
  | .error reason => reason.contains "capacity must be in 1..64"
  | .ok _ => false

#guard
  match ProofForge.Wasm.Near.Codec.inputPlan (.boundedString 65) with
  | .error reason => reason.contains "capacity must be in 1..64"
  | .ok _ => false

#guard ProofForge.Wasm.Near.Registry.digestOf "Counter" == some "121a0c8f7e697642"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearCtx" == some "8233f27ab39f6133"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearBytes" == some "2acf0192ce0f84a8"
