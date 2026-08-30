import Examples.NearPromise
import Lean
import ProofForge

/-! Static detached/returned Promise extraction, projection, and WAT invariants. -/

namespace Tests.NearPromiseSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.accountIdLiteralValid "aa"
#guard Codec.accountIdLiteralValid "receiver.test.near"
#guard Codec.accountIdLiteralValid "a-b_c.d"
#guard !Codec.accountIdLiteralValid "a"
#guard !Codec.accountIdLiteralValid "Receiver.test.near"
#guard !Codec.accountIdLiteralValid "-receiver.test.near"
#guard !Codec.accountIdLiteralValid "receiver..test.near"
#guard !Codec.accountIdLiteralValid "receiver.test.near-"
#guard Codec.promiseMethodLiteralValid "record"
#guard !Codec.promiseMethodLiteralValid ""
#guard Codec.promiseMethodLiteralValid (String.ofList (List.replicate 256 'a'))
#guard !Codec.promiseMethodLiteralValid (String.ofList (List.replicate 257 'a'))

private partial def promiseSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.promiseFunctionCallDetached receiver method capacity arguments _ _ _)) =>
          #[s!"detached.{receiver}.{method}.{capacity}.{arguments.size}"]
      | .ext (.near (.promiseFunctionCallReturned receiver method capacity arguments _ _ _)) =>
          #[s!"returned.{receiver}.{method}.{capacity}.{arguments.size}"]
      | .ite _ _ _ thn els => promiseSteps thn ++ promiseSteps els
      | .forBody _ body => promiseSteps body
      | _ => #[]

elab "#pf_near_promise_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearPromise with
    | .ok program => pure program
    | .error reason => throwError reason
  let steps := source.methods.foldl (init := #[]) fun acc method => acc ++ promiseSteps method.ops
  let detachedRecord := "detached.receiver.test.near.record.8.9"
  let detachedMissing := "detached.receiver.test.near.missing.8.9"
  let returnedRecord := "returned.receiver.test.near.recordValue.8.9"
  let returnedMissing := "returned.receiver.test.near.missing.8.9"
  unless steps.size == 7 && (steps.filter (· == detachedRecord)).size == 4 &&
      (steps.filter (· == detachedMissing)).size == 1 &&
      (steps.filter (· == returnedRecord)).size == 1 &&
      (steps.filter (· == returnedMissing)).size == 1 do
    throwError s!"extractor lost or duplicated promise effects: {repr steps}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  for method in program.entries do
    match Emit.emit { program with entries := #[method] } with
    | .ok _ => pure ()
    | .error reason => throwError s!"{method.ixName}: {reason}"
  let send ← match program.entries.find? (·.ixName == "send") with
    | some method => pure method
    | none => throwError "missing send entry"
  let sendWat ← match Emit.emit { program with entries := #[send] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  if sendWat.contains "promise_return" then
    throwError "detached Promise method unexpectedly imports or calls promise_return"
  let sendReturned ← match program.entries.find? (·.ixName == "sendReturned") with
    | some method => pure method
    | none => throwError "missing sendReturned entry"
  let returnedWat ← match Emit.emit { program with entries := #[sendReturned] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  match returnedWat.splitOn "(call $pf_promise_batch_action_function_call" with
  | [_beforeAction, afterAction] =>
      match afterAction.splitOn "(call $pf_promise_return" with
      | [between, _afterReturn] =>
          unless between.contains "(call $pf_storage_write" do
            throwError "returned Promise was linked before caller-state persistence"
      | _ => throwError "returned Promise method must call promise_return exactly once"
  | _ => throwError "returned Promise method must schedule exactly one function-call action"
  if returnedWat.contains "(call $pf_value_return" then
    throwError "returned Promise method must not overwrite promise_return with value_return"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"promise_batch_create\"",
    "(import \"env\" \"promise_batch_action_function_call\"",
    "(import \"env\" \"promise_return\"",
    "(func (export \"send\")",
    "(func (export \"sendMissing\")",
    "(func (export \"sendReturned\")",
    "(func (export \"sendReturnedMissing\")",
    "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
    "(i64.store (i32.wrap_i64",
    "(i32.const 8))",
    "(call $pf_promise_batch_create (i64.const 18) (i64.const 8192))",
    "(call $pf_promise_batch_action_function_call",
    "(call $pf_promise_return",
    "(i64.const 6) (i64.const 8210)",
    "(i64.const 7) (i64.const 8216)",
    "(i64.const 11) (i64.const 8223)",
    "(i64.const 20000000000000)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR Promise WAT missing {anchor}\n{wat}"
  let viewCall := { source with methods := source.methods.map fun method =>
    if method.ixName == "send" then { method with kind := .get } else method }
  match IR.fromExtracted viewCall >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong view-promise rejection: {reason}"
  | .ok _ => throwError "detached Promise call was accepted in a view"
  let viewReturned := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendReturned" then { method with kind := .get } else method }
  match IR.fromExtracted viewReturned >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong returned-view rejection: {reason}"
  | .ok _ => throwError "returned Promise call was accepted in a view"
  let doubleReturned := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendReturned" then
      { method with ops := method.ops.flatMap fun op =>
          match op with
          | .ext (.near (.promiseFunctionCallReturned _ _ _ _ _ _ _)) => #[op, op]
          | _ => #[op] }
    else method }
  match IR.fromExtracted doubleReturned >>= Emit.emit with
  | .error reason =>
      unless reason.contains "cannot return more than one promise" do
        throwError s!"wrong double-returned-Promise rejection: {reason}"
  | .ok _ => throwError "two returned Promises were accepted on one execution path"
  logInfo m!"proofforge-near-promise: digest = {IR.digestHex program}"

#pf_near_promise_check

end Tests.NearPromiseSpec
