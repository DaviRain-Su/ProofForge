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

private def isExpectedBoundedLogOps (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  match method.ops with
  | #[.ext (.logUtf8Bounded 8 message), .returnU64 (.arg 0)] =>
      message == #[.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6, .arg 7, .arg 8]
  | _ => false

private def isExpectedEventOps (method : ProofForge.Wasm.Near.IR.Method) : Bool :=
  match method.ops with
  | #[.ext (.nep297StringData "proof_forge" "1.0.0" "string_data" 8 data),
      .returnU64 (.arg 0)] =>
      data == #[.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6, .arg 7, .arg 8]
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
  let some rawLog := extracted.methods.find? (·.ixName == "logString")
    | throwError "missing extracted logString"
  let some rawEvent := extracted.methods.find? (·.ixName == "eventString")
    | throwError "missing extracted eventString"
  unless rawBytes.paramCount == 1 && rawBytes.paramSchemas == #[.boundedBytes 8] &&
      rawString.paramCount == 1 && rawString.paramSchemas == #[.boundedString 8] &&
      rawLog.paramCount == 1 && rawLog.paramSchemas == #[.boundedString 8] &&
      rawEvent.paramCount == 1 && rawEvent.paramSchemas == #[.boundedString 8] do
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
  let some logString := program.entries.find? (·.ixName == "logString")
    | throwError "missing lowered logString"
  let some eventString := program.entries.find? (·.ixName == "eventString")
    | throwError "missing lowered eventString"
  unless bytes.paramCount == 9 && bytes.inputSchema == some (.boundedBytes 8) &&
      bytes.inputPolicy == "near-borsh-bytes-v1(capacity=8)" &&
      text.paramCount == 9 && text.inputSchema == some (.boundedString 8) &&
      text.inputPolicy == "near-borsh-string-v1(capacity=8)" &&
      logString.paramCount == 9 && logString.inputSchema == some (.boundedString 8) &&
      logString.inputPolicy == "near-borsh-string-v1(capacity=8)" &&
      eventString.paramCount == 9 && eventString.inputSchema == some (.boundedString 8) &&
      eventString.inputPolicy == "near-borsh-string-v1(capacity=8)" &&
      isExpectedBoundedOps bytes && isExpectedBoundedOps text &&
      isExpectedBoundedLogOps logString && isExpectedEventOps eventString do
    throwError s!"wrong NEAR bounded scalar frame, policy, or rewritten operations: " ++
      ProofForge.Wasm.IR.opsCanon ProofForge.Wasm.Near.IR.extValCanon
        ProofForge.Wasm.Near.IR.extOpCanon logString.ops
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok source => pure source
    | .error reason => throwError reason
  let anchors : Array String := #[
    "(func $pf_utf8_valid (param $ptr i32) (param $len i32) (result i32)",
    "(import \"env\" \"log_utf8\" (func $pf_log_utf8 (param i64 i64)))",
    "(local.set $pf_input_size (call $pf_register_len (i64.const 0)) )",
    "(if (i64.lt_u (local.get $pf_input_size) (i64.const 4))",
    "(if (i64.gt_u (local.get $pf_input_size) (i64.const 12))",
    "(call $pf_read_register (i64.const 0) (i64.const 256))",
    "(local.set $pf_p0 (i64.load32_u (i32.const 256)) )",
    "(if (i64.gt_u (local.get $pf_p0) (i64.const 8))",
    "(if (i64.ne (local.get $pf_input_size) (i64.add (i64.const 4) (local.get $pf_p0)))",
    "(call $pf_utf8_valid (i32.const 260) (i32.wrap_i64 (local.get $pf_p0)))",
    "(func (export \"logString\")",
    "(call $pf_arena_alloc (i64.const 8) (i64.const 1))",
    "(if (i64.gt_u (local.get $pf_r0) (i64.const 8)) (then unreachable))",
    "(if (i64.gt_u (local.get $pf_p1) (i64.const 255)) (then unreachable))",
    "(call $pf_log_utf8 (local.get $pf_r0) (local.get $pf_r1))",
    "(func (export \"eventString\")",
    "(func (export \"eventEscapedMetadata\")",
    "(call $pf_arena_alloc (i64.const 135) (i64.const 1))",
    "(i64.const 69)",
    "(i64.const 92)",
    "(i64.const 117)",
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
#guard ProofForge.Wasm.Near.Registry.digestOf "NearBytes" == some "3b15034031dcf0a2"
