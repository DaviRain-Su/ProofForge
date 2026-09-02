import Examples.Near.NearJsonUnitOutput
import Examples.Near.NearPromise
import Lean
import ProofForge

namespace Tests.NearJsonUnitOutputSpec

open Lean Elab Command

private partial def hasUnitTerminal : Array ProofForge.Extract.IR.Op → Bool :=
  (·.any fun op => match op with
    | .okState (.lit 0) => true
    | .ite _ _ _ thn els => hasUnitTerminal thn || hasUnitTerminal els
    | _ => false)

elab "#pf_near_json_unit_output_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonUnitOutput with
    | .ok program => pure program
    | .error reason => throwError reason
  let some method := source.methods.find? (·.ixName == "setMarker")
    | throwError "missing setMarker"
  unless method.kind == .increment && method.retSchema == .unit && method.retCount == 0 &&
      hasUnitTerminal method.ops do
    throwError "extractor did not retain exact zero-leaf Unit result with a success terminal"
  let program ← match ProofForge.Wasm.Near.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some target := program.entries.find? (·.ixName == "setMarker")
    | throwError "missing target setMarker"
  unless target.kind == .increment && target.tupleArity.isNone && !target.echoDropped &&
      target.outputSchema == some .unit &&
      target.outputPolicy == "near-json-null-unit-v1" do
    throwError "NEAR target lost JSON null Unit output metadata or mutating classification"
  let some voidTarget := program.entries.find? (·.ixName == "setMarkerVoid")
    | throwError "missing target setMarkerVoid"
  unless voidTarget.kind == .increment && voidTarget.tupleArity.isNone &&
      !voidTarget.echoDropped && voidTarget.outputSchema == some .unit &&
      voidTarget.outputPolicy == "near-void-empty-v1" do
    throwError "NEAR target lost empty Unit output metadata or mutating classification"
  let malformed := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setMarker" then { candidate with retCount := 1 } else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted malformed with
  | .error reason =>
      unless reason.contains "output frame does not match its JSON null Unit plan" do
        throwError s!"wrong malformed Unit frame rejection: {reason}"
  | .ok _ => throwError "malformed Unit output frame was accepted"
  let viewUnit := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setMarker" then { candidate with kind := .get } else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted viewUnit with
  | .error reason =>
      unless reason.contains "JSON null Unit output requires a mutating entry" do
        throwError s!"wrong Unit view rejection: {reason}"
  | .ok _ => throwError "Unit view incorrectly selected the mutating JSON null policy"
  let viewVoid := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setMarkerVoid" then { candidate with kind := .get } else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted viewVoid with
  | .error reason =>
      unless reason.contains "empty return requires a mutating entry" do
        throwError s!"wrong empty-return view rejection: {reason}"
  | .ok _ => throwError "empty return was accepted on a view"
  let malformedVoid := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setMarkerVoid" then
      { candidate with retSchema := .scalar .uint64, retCount := 1 }
    else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted malformedVoid with
  | .error reason =>
      unless reason.contains "empty return requires an exact zero-leaf Unit result" do
        throwError s!"wrong malformed empty-return rejection: {reason}"
  | .ok _ => throwError "empty return accepted a scalar public result"
  let duplicateVoid := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "setMarkerVoid" then
      { candidate with annotations := candidate.annotations.push "near.void.v1" }
    else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted duplicateVoid with
  | .error reason =>
      unless reason.contains "duplicate near void annotations" do
        throwError s!"wrong duplicate empty-return rejection: {reason}"
  | .ok _ => throwError "duplicate empty-return annotation was accepted"
  let voidInitializer := { source with methods := source.methods.map fun candidate =>
    if candidate.kind == .init then
      { candidate with annotations := candidate.annotations.push "near.void.v1" }
    else candidate }
  match ProofForge.Wasm.Near.IR.fromExtracted voidInitializer with
  | .error reason =>
      unless reason.contains "empty return requires a mutating entry" do
        throwError s!"wrong initializer empty-return rejection: {reason}"
  | .ok _ => throwError "empty return annotation was accepted on an initializer"
  let wat ← match ProofForge.Wasm.Near.Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let parts := wat.splitOn "(func (export \"setMarker\")"
  unless parts.length == 2 do throwError "missing unique setMarker export"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  let anchors := #[
    "(local $pf_output_ptr i32)",
    "(call $pf_arena_alloc (i64.const 4) (i64.const 1))",
    "(i32.store (local.get $pf_output_ptr) (i32.const 1819047278))",
    "(call $pf_value_return (i64.const 4) (i64.extend_i32_u (local.get $pf_output_ptr)))"
  ]
  for anchor in anchors do
    unless body.contains anchor do throwError s!"JSON null Unit WAT missing {anchor}"
  unless (body.splitOn "(call $pf_value_return").length == 2 do
    throwError "JSON null Unit wrapper must issue exactly one value_return"
  if body.contains "(call $pf_value_return (i64.const 8)" then
    throwError "JSON null Unit wrapper leaked the synthetic scalar carrier"
  let voidParts := wat.splitOn "(func (export \"setMarkerVoid\")"
  unless voidParts.length == 2 do throwError "missing unique setMarkerVoid export"
  let voidBody := (voidParts[1]!).splitOn "(func (export \"" |>.head!
  unless voidBody.contains "(call $pf_storage_write" &&
      !voidBody.contains "(call $pf_value_return" &&
      !voidBody.contains "(call $pf_arena_alloc (i64.const 4)" do
    throwError "empty Unit wrapper must persist state without allocating or calling value_return"
  let promiseSource ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearPromise with
    | .ok program => pure program
    | .error reason => throwError reason
  let promiseMethods := promiseSource.methods.map fun candidate =>
    if candidate.ixName == "transferCallerReturned" then
      { candidate with
        retSchema := .unit
        retCount := 0
        retTypes := #[]
        annotations := candidate.annotations.push "near.void.v1" }
    else candidate
  let promiseVoid := { promiseSource with methods := promiseMethods }
  let promiseProgram ← match ProofForge.Wasm.Near.IR.fromExtracted promiseVoid with
    | .ok program => pure program
    | .error reason => throwError reason
  match ProofForge.Wasm.Near.Emit.emit promiseProgram with
  | .error reason =>
      unless reason.contains "empty Unit output cannot also return a promise" do
        throwError s!"wrong void/Promise rejection: {reason}"
  | .ok _ => throwError "empty output was incorrectly combined with promise_return"
  let touchParts := wat.splitOn "(func (export \"get\")"
  unless touchParts.length == 2 &&
      (touchParts[1]!).contains "(call $pf_value_return (i64.const 8) (i64.const 0))" do
    throwError "raw UInt64 view output changed while adding JSON Unit output"
  logInfo m!"proofforge-near-json-unit-output: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_near_json_unit_output_check

end Tests.NearJsonUnitOutputSpec
