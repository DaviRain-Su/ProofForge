import Examples.NearPromiseResult
import Lean
import ProofForge

/-! Bounded NEAR callback-result extraction, projection, and WAT invariants. -/

namespace Tests.NearPromiseResultSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.wellFormed 1
#guard ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.wellFormed 64
#guard !ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.wellFormed 0
#guard !ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.wellFormed 65

private partial def resultReads : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun reads op =>
      reads ++ match op with
      | .ext (.near (.promiseResultRead capacity index)) =>
          #[s!"read.{capacity}.{repr index}"]
      | .ite _ _ _ thn els => resultReads thn ++ resultReads els
      | .forBody _ body => resultReads body
      | _ => #[]

private partial def usesResultCount : ProofForge.Extract.IR.Val → Bool
  | .ext (.near .promiseResultsCount) _ => true
  | .field base _ | .bitNot base => usesResultCount base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      usesResultCount lhs || usesResultCount rhs
  | .indexGet base _ index _ _ => usesResultCount base || usesResultCount index
  | .select _ lhs rhs thn els =>
      usesResultCount lhs || usesResultCount rhs || usesResultCount thn || usesResultCount els
  | .ext _ operands => operands.any usesResultCount
  | _ => false

private partial def opUsesResultCount : ProofForge.Extract.IR.Op → Bool
  | .letLocal _ value | .setLocal _ value | .storeField _ value | .okState value
  | .returnU64 value | .returnState value => usesResultCount value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      usesResultCount lhs || usesResultCount rhs
  | .ite _ lhs rhs thn els =>
      usesResultCount lhs || usesResultCount rhs || thn.any opUsesResultCount ||
        els.any opUsesResultCount
  | .forBody _ body => body.any opUsesResultCount
  | _ => false

elab "#pf_near_promise_result_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearPromiseResult with
    | .ok program => pure program
    | .error reason => throwError reason
  let reads := source.methods.foldl (init := #[]) fun acc method => acc ++ resultReads method.ops
  unless reads.size == 6 && (reads.filter (·.startsWith "read.8.")).size == 4 &&
      (reads.filter (·.startsWith "read.4.")).size == 2 do
    throwError s!"extractor lost or duplicated Promise-result reads: {repr reads}"
  let some countMethod := source.methods.find? (·.ixName == "resultsCount")
    | throwError "missing resultsCount"
  unless countMethod.ops.any opUsesResultCount do
    throwError "extractor lost promiseResultsCount"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"promise_results_count\" (func $pf_promise_results_count (result i64)))",
    "(import \"env\" \"promise_result\" (func $pf_promise_result (param i64 i64) (result i64)))",
    "(global $pf_promise_result_active (mut i32)",
    "(func $pf_promise_result_byte",
    "(call $pf_promise_results_count)",
    "(call $pf_promise_result (i64.const 0) (i64.const 4))",
    "(if (i64.gt_u (global.get $pf_promise_result_status) (i64.const 2))",
    "(if (i64.eq (global.get $pf_promise_result_status) (i64.const 1))",
    "(global.set $pf_promise_result_length (call $pf_register_len (i64.const 4))",
    "(if (i64.gt_u (global.get $pf_promise_result_length) (i64.const 4))",
    "(call $pf_arena_alloc (global.get $pf_promise_result_length) (i64.const 1))",
    "(call $pf_read_register (i64.const 4)",
    "(i64.eq (global.get $pf_promise_result_status) (i64.const 1))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR Promise-result WAT missing {anchor}\n{wat}"
  let some count := program.entries.find? (·.ixName == "resultsCount")
    | throwError "missing lowered resultsCount"
  let countWat ←
    match Emit.emit { program with entries := #[count] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless countWat.contains "promise_results_count" && !countWat.contains "\"promise_result\"" do
    throwError "count-only module did not prune the Promise-result read import"
  let some status := program.entries.find? (·.ixName == "resultStatus")
    | throwError "missing lowered resultStatus"
  let readWat ←
    match Emit.emit { program with entries := #[status] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless readWat.contains "\"promise_result\"" && !readWat.contains "promise_results_count" do
    throwError "read-only module did not prune the Promise-result count import"
  let viewCount := { source with methods := source.methods.map fun method =>
    if method.ixName == "resultsCount" then { method with kind := .get } else method }
  match IR.fromExtracted viewCount >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot count promise results" do
        throwError s!"wrong view-count rejection: {reason}"
  | .ok _ => throwError "Promise-result count was accepted in a view"
  let viewRead := { source with methods := source.methods.map fun method =>
    if method.ixName == "resultStatus" then { method with kind := .get } else method }
  match IR.fromExtracted viewRead >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot read promise results" do
        throwError s!"wrong view-result rejection: {reason}"
  | .ok _ => throwError "Promise-result read was accepted in a view"
  logInfo m!"proofforge-near-promise-result: digest = {IR.digestHex program}"

#pf_near_promise_result_check

end Tests.NearPromiseResultSpec
