import Examples.NearPromise
import Lean
import ProofForge

/-! Static detached/returned Promise and one self-callback edge extraction/WAT invariants. -/

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
      | .ext (.near (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
          childCapacity callbackCapacity childArguments callbackArguments _ _ _ _ _ _)) =>
          #[s!"then.{receiver}.{childMethod}.{callbackMethod}." ++
            s!"{childCapacity}.{callbackCapacity}.{childArguments.size}.{callbackArguments.size}"]
      | .ite _ _ _ thn els => promiseSteps thn ++ promiseSteps els
      | .forBody _ body => promiseSteps body
      | _ => #[]

private partial def resultDecodesVal : ProofForge.Extract.IR.Val → Array Nat
  | .ext (.near (.promiseResultBorshUInt64D capacity)) operands =>
      #[capacity] ++ operands.flatMap resultDecodesVal
  | .ext _ operands => operands.flatMap resultDecodesVal
  | .field base _ | .bitNot base => resultDecodesVal base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      resultDecodesVal lhs ++ resultDecodesVal rhs
  | .indexGet base _ index _ _ => resultDecodesVal base ++ resultDecodesVal index
  | .select _ lhs rhs thn els =>
      resultDecodesVal lhs ++ resultDecodesVal rhs ++
        resultDecodesVal thn ++ resultDecodesVal els
  | _ => #[]

private partial def resultDecodes : Array ProofForge.Extract.IR.Op → Array Nat
  | ops => ops.foldl (init := #[]) fun decodes op =>
      decodes ++ match op with
      | .letLocal _ value | .setLocal _ value | .storeField _ value | .okState value
      | .returnU64 value | .returnState value => resultDecodesVal value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
          resultDecodesVal lhs ++ resultDecodesVal rhs
      | .ite _ lhs rhs thn els =>
          resultDecodesVal lhs ++ resultDecodesVal rhs ++
            resultDecodes thn ++ resultDecodes els
      | .forBody _ body => resultDecodes body
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
  let thenSuccess := "then.receiver.test.near.recordValue.callbackSuccess.8.8.9.9"
  let thenFailure := "then.receiver.test.near.missing.callbackFailure.8.8.9.9"
  let thenOversized := "then.receiver.test.near.recordValue.callbackOversized.8.8.9.9"
  unless steps.size == 10 && (steps.filter (· == detachedRecord)).size == 4 &&
      (steps.filter (· == detachedMissing)).size == 1 &&
      (steps.filter (· == returnedRecord)).size == 1 &&
      (steps.filter (· == returnedMissing)).size == 1 &&
      (steps.filter (· == thenSuccess)).size == 1 &&
      (steps.filter (· == thenFailure)).size == 1 &&
      (steps.filter (· == thenOversized)).size == 1 do
    throwError s!"extractor lost or duplicated promise effects: {repr steps}"
  let decodes := source.methods.foldl (init := #[]) fun acc method =>
    acc ++ resultDecodes method.ops
  unless decodes.size == 3 && (decodes.filter (· == 8)).size == 2 &&
      (decodes.filter (· == 4)).size == 1 do
    throwError s!"extractor lost strict callback UInt64 decoders: {repr decodes}"
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
  if returnedWat.contains "promise_batch_then" || returnedWat.contains "current_account_id" then
    throwError "plain returned Promise unexpectedly retained callback-only imports"
  let sendThenSuccess ← match program.entries.find? (·.ixName == "sendThenSuccess") with
    | some method => pure method
    | none => throwError "missing sendThenSuccess entry"
  let thenWat ← match Emit.emit { program with entries := #[sendThenSuccess] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  match thenWat.splitOn "(call $pf_promise_batch_then" with
  | [beforeThen, afterThen] =>
      unless beforeThen.contains "(call $pf_promise_batch_create" &&
          beforeThen.contains "(call $pf_promise_batch_action_function_call" do
        throwError "callback dependency was created before the child function-call action"
      match afterThen.splitOn "(call $pf_promise_batch_action_function_call" with
      | [_beforeCallbackAction, afterCallbackAction] =>
          match afterCallbackAction.splitOn "(call $pf_promise_return" with
          | [beforeReturn, _afterReturn] =>
              unless beforeReturn.contains "(call $pf_storage_write" do
                throwError "callback Promise was returned before caller-state persistence"
          | _ => throwError "callback chain must return exactly one Promise"
      | _ => throwError "callback chain must append exactly one callback action after then"
  | _ => throwError "callback chain must call promise_batch_then exactly once"
  for anchor in #[
      "(import \"env\" \"promise_batch_then\" " ++
        "(func $pf_promise_batch_then (param i64 i64 i64) (result i64)))",
      "(import \"env\" \"current_account_id\" " ++
        "(func $pf_current_account_id (param i64)))",
      "(call $pf_current_account_id (i64.const 3))",
      "(call $pf_read_register (i64.const 3) (i64.const 128))",
      "(call $pf_promise_batch_then",
      "(local.get $pf_self_len) (i64.const 128)" ] do
    unless thenWat.contains anchor do
      throwError s!"NEAR callback WAT missing {anchor}\n{thenWat}"
  let callbackSuccess ← match program.entries.find? (·.ixName == "callbackSuccess") with
    | some method => pure method
    | none => throwError "missing callbackSuccess entry"
  let callbackSuccessWat ← match Emit.emit { program with entries := #[callbackSuccess] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(import \"env\" \"predecessor_account_id\"",
      "(import \"env\" \"current_account_id\"",
      "(i64.eq (local.get $pf_pred_len) (local.get $pf_self_len))",
      "(i64.eq (local.get $pf_pred) (local.get $pf_self))",
      "(i64.eq (local.get $pf_pred1) (local.get $pf_self1))",
      "(i64.eq (local.get $pf_pred2) (local.get $pf_self2))",
      "(i64.eq (local.get $pf_pred3) (local.get $pf_self3))",
      "(i64.eq (local.get $pf_pred4) (local.get $pf_self4))",
      "(i64.eq (local.get $pf_pred5) (local.get $pf_self5))",
      "(i64.eq (local.get $pf_pred6) (local.get $pf_self6))",
      "(i64.eq (local.get $pf_pred7) (local.get $pf_self7))",
      "(i64.eq (call $pf_promise_result_status (i64.const 8)) (i64.const 1))",
      "(i64.ne (call $pf_promise_result_fits (i64.const 8)) (i64.const 0))",
      "(i64.eq (call $pf_promise_result_length (i64.const 8)) (i64.const 8))",
      "(call $pf_promise_result_byte (i64.const 8) (i64.const 7))",
      "(i64.const 56)",
      "(else (i64.const 0))",
      "(i64.store (i32.const 0) (local.get $pf_v0))" ] do
    unless callbackSuccessWat.contains anchor do
      throwError s!"strict callback UInt64 WAT missing {anchor}\n{callbackSuccessWat}"
  if callbackSuccessWat.contains "(local.set $marker (local.get $pf_v0))" then
    throwError "callback tuple result overwrote its independently persisted state field"
  let callbackBody ← match callbackSuccessWat.splitOn "(func (export \"callbackSuccess\")" with
    | [_preamble, body] => pure body
    | _ => throwError "callbackSuccess WAT must contain exactly one exported body"
  let afterPredecessor ← match callbackBody.splitOn "(call $pf_predecessor_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackSuccess must read predecessor exactly once"
  let afterCurrent ← match afterPredecessor.splitOn "(call $pf_current_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackSuccess must read current account after predecessor"
  unless afterCurrent.contains
      "(then\n        (global.set $pf_promise_result_active (i32.const 1))" do
    throwError "callback result read is not dominated by the self-call guard"
  unless afterCurrent.contains
      "(else\n        (call $pf_panic_utf8 (i64.const 8) (i64.const 2048))\n      ))" do
    throwError "callback self-call rejection must panic before state persistence"
  match afterCurrent.splitOn "(call $pf_promise_result (i64.const 0)" with
  | [_beforeRead, _afterRead] => pure ()
  | _ => throwError "callbackSuccess must read its Promise result exactly once after identity loads"
  let callbackFailure ← match program.entries.find? (·.ixName == "callbackFailure") with
    | some method => pure method
    | none => throwError "missing callbackFailure entry"
  let callbackFailureWat ← match Emit.emit { program with entries := #[callbackFailure] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless callbackFailureWat.contains "(else (i64.const 999))" do
    throwError "failed callback lost its explicit UInt64 decode fallback"
  let callbackOversized ← match program.entries.find? (·.ixName == "callbackOversized") with
    | some method => pure method
    | none => throwError "missing callbackOversized entry"
  let callbackOversizedWat ← match Emit.emit { program with entries := #[callbackOversized] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  unless callbackOversizedWat.contains
      "(i64.ne (call $pf_promise_result_fits (i64.const 4)) (i64.const 0))" &&
      callbackOversizedWat.contains "(else (i64.const 999))" do
    throwError "oversized callback lost its capacity-4 UInt64 decode fallback"
  for (name, callbackWat) in #[
      ("callbackFailure", callbackFailureWat),
      ("callbackOversized", callbackOversizedWat) ] do
    for anchor in #[
        "(call $pf_predecessor_account_id",
        "(call $pf_current_account_id",
        "(i64.eq (local.get $pf_pred_len) (local.get $pf_self_len))",
        "(i64.eq (local.get $pf_pred) (local.get $pf_self))",
        "(i64.eq (local.get $pf_pred7) (local.get $pf_self7))",
        "(else\n        (call $pf_panic_utf8 (i64.const 8) (i64.const 2048))" ] do
      unless callbackWat.contains anchor do
        throwError s!"{name} lost private self-call guard anchor {anchor}"
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
    "(func (export \"sendThenSuccess\")",
    "(func (export \"sendThenMissing\")",
    "(func (export \"sendThenOversized\")",
    "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
    "(i64.store (i32.wrap_i64",
    "(i32.const 8))",
    "(call $pf_promise_batch_create (i64.const 18) (i64.const 8192))",
    "(call $pf_promise_batch_action_function_call",
    "(call $pf_promise_batch_then",
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
  let viewThen := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendThenSuccess" then { method with kind := .get } else method }
  match IR.fromExtracted viewThen >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong callback-view rejection: {reason}"
  | .ok _ => throwError "callback Promise chain was accepted in a view"
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
