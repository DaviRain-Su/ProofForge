import Examples.NearJsonU128Mutation
import Examples.NearPromise
import Lean
import ProofForge

namespace Tests.NearJsonU128MutationSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private partial def sourceReturns : Array ProofForge.Extract.IR.Op → Nat
  | ops => ops.foldl (init := 0) fun count op =>
    match op with
    | .returnU64 _ => count + 1
    | .ite _ _ _ thn els => count + sourceReturns thn + sourceReturns els
    | .forBody _ body => count + sourceReturns body
    | _ => count

private partial def targetReturns : Array ProofForge.Wasm.Near.Ops.Op → Nat
  | ops => ops.foldl (init := 0) fun count op =>
    match op with
    | .returnU64 _ => count + 1
    | .ite _ _ _ thn els => count + targetReturns thn + targetReturns els
    | .forBody _ body => count + targetReturns body
    | _ => count

private partial def replaceTargetResult : Array ProofForge.Wasm.Near.Ops.Op →
    Array ProofForge.Wasm.Near.Ops.Op
  | ops => ops.flatMap fun op =>
      match op with
      | .okState _ => #[.returnU64 (.lit 2), .returnU64 (.lit 1)]
      | .ite cmp lhs rhs thn els =>
          #[.ite cmp lhs rhs (replaceTargetResult thn) (replaceTargetResult els)]
      | .forBody index body => #[.forBody index (replaceTargetResult body)]
      | _ => #[op]

elab "#pf_near_json_u128_mutation_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearJsonU128Mutation with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceCommit := source.methods.find? (·.ixName == "commitAsymmetric")
    | throwError "missing source commitAsymmetric"
  unless sourceCommit.kind == .increment && sourceCommit.retSchema == .scalar .uint128 &&
      sourceCommit.retCount == 2 && sourceReturns sourceCommit.ops == 2 do
    throwError s!"extractor lost mutating two-leaf UInt128 result: schema={repr sourceCommit.retSchema} count={sourceCommit.retCount} returns={sourceReturns sourceCommit.ops}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some commit := program.entries.find? (·.ixName == "commitAsymmetric")
    | throwError "missing target commitAsymmetric"
  unless commit.kind == .increment && commit.outputSchema == some (.scalar .uint128) &&
      commit.outputPolicy == "near-json-u128-string-v1" && commit.tupleArity == some 2 &&
      targetReturns commit.ops == 2 do
    throwError "target lost mutating quoted-u128 output policy"
  let malformed := { source with methods := source.methods.map fun method =>
    if method.ixName == "commitAsymmetric" then { method with retCount := 1 } else method }
  match IR.fromExtracted malformed with
  | .error reason =>
      unless reason.contains "output frame does not match its JSON u128 plan" do
        throwError s!"wrong mutating u128 frame rejection: {reason}"
  | .ok _ => throwError "malformed mutating u128 frame was accepted"
  let ordinaryRecordSchema : ProofForge.Core.Codec.Schema :=
    .record "OrdinaryPair" #[
      ("left", .scalar .uint64), ("right", .scalar .uint64)]
  let ordinaryRecord := { source with methods := source.methods.map fun method =>
    if method.ixName == "commitAsymmetric" then
      { method with retSchema := ordinaryRecordSchema }
    else method }
  match IR.fromExtracted ordinaryRecord with
  | .error _ => pure ()
  | .ok ordinaryProgram =>
      let some ordinaryMethod := ordinaryProgram.entries.find? (·.ixName == "commitAsymmetric")
        | throwError "ordinary-record program lost commitAsymmetric"
      if ordinaryMethod.outputPolicy == "near-json-u128-string-v1" ||
          ordinaryMethod.outputSchema == some (.scalar .uint128) then
        throwError "ordinary two-field record selected mutating JSON u128 output"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let parts := wat.splitOn "(func (export \"commitAsymmetric\")"
  unless parts.length == 2 do throwError "missing unique commitAsymmetric export"
  let body := (parts[1]!).splitOn "(func (export \"" |>.head!
  let leftWrite := body.splitOn "(call $pf_storage_write"
  unless leftWrite.length == 3 do
    throwError "mutating u128 body must persist exactly two state fields"
  match body.splitOn "(call $pf_value_return" with
  | [before, _after] =>
      unless (before.splitOn "(call $pf_storage_write").length == 3 &&
          before.contains "(i64.const 9833440827789222417)" &&
          before.contains "(i64.const 2)" && before.contains "(i64.const 1)" do
        throwError "mutating u128 state writes or independent result constants lost before value_return"
  | _ => throwError "mutating u128 body must issue exactly one value_return"
  unless body.contains "(call $pf_arena_alloc (i64.const 41) (i64.const 1))" &&
      body.contains "(call $pf_u128_decimal (i64.const 2) (i64.const 1)" &&
      (body.splitOn "(call $pf_attached_deposit").length == 2 &&
      body.contains "(i64.load (i32.const 24))" && body.contains "(i64.load (i32.const 32))" do
    throwError "mutating u128 output lost non-payable guard, asymmetric limb order, or geometry"
  let promiseSource ← match ProofForge.Extract.extractModuleIR env `Examples.NearPromise with
    | .ok source => pure source
    | .error reason => throwError reason
  let promiseProgram ← match IR.fromExtracted promiseSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let u128Schema : ProofForge.Core.Codec.Schema := .scalar .uint128
  let promiseEntries := promiseProgram.entries.map fun method =>
    if method.ixName == "transferCallerReturned" then
      { method with
        outputSchema := some u128Schema
        outputPolicy := "near-json-u128-string-v1"
        tupleArity := some 2
        ops := replaceTargetResult method.ops }
    else method
  match Emit.emit { promiseProgram with entries := promiseEntries } with
  | .error reason =>
      unless reason.contains "JSON u128 output cannot also return a promise" do
        throwError s!"wrong Promise/u128 rejection: {reason}"
  | .ok _ => throwError "mutating u128 output was combined with promise_return"
  logInfo m!"proofforge-near-json-u128-mutation: digest = {IR.digestHex program}"

#pf_near_json_u128_mutation_check

end Tests.NearJsonU128MutationSpec
