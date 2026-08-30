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
      | .ext (.near (.promiseTransferDetached receiver _ _)) =>
          #[s!"transfer.detached.{receiver}"]
      | .ext (.near (.promiseTransferReturned receiver _ _)) =>
          #[s!"transfer.returned.{receiver}"]
      | .ext (.near (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
          childCapacity callbackCapacity childArguments callbackArguments _ _ _ _ _ _)) =>
          #[s!"then.{receiver}.{childMethod}.{callbackMethod}." ++
            s!"{childCapacity}.{callbackCapacity}.{childArguments.size}.{callbackArguments.size}"]
      | .ext (.near (.promiseFunctionCallAndThenReturned
          leftReceiver leftMethod rightReceiver rightMethod callbackMethod
          leftCapacity rightCapacity callbackCapacity
          leftArguments rightArguments callbackArguments _ _ _ _ _ _ _ _ _)) =>
          #[s!"and.{leftReceiver}.{leftMethod}.{rightReceiver}.{rightMethod}.{callbackMethod}." ++
            s!"{leftCapacity}.{rightCapacity}.{callbackCapacity}." ++
            s!"{leftArguments.size}.{rightArguments.size}.{callbackArguments.size}"]
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

namespace PrivateView

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (value : UInt64) : State := { value }

@[pf_entry]
def set (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ value }, value)

@[pf_entry, pf_near_private]
def secret (state : State) : UInt64 := state.value

end PrivateView

namespace PayableView

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (value : UInt64) : State := { value }

@[pf_entry]
def set (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ value }, value)

@[pf_entry, pf_near_payable]
def invalid (state : State) : UInt64 := state.value

end PayableView

elab "#pf_near_promise_check" : command => do
  let env ← getEnv
  let privateViewSource ←
    match ProofForge.Extract.extractModuleIR env `Tests.NearPromiseSpec.PrivateView with
    | .ok program => pure program
    | .error reason => throwError reason
  match ProofForge.Svm.IR.fromExtracted privateViewSource with
  | .error reason =>
      unless reason.contains "cannot consume foreign target annotations" do
        throwError s!"wrong SVM foreign-policy rejection: {reason}"
  | .ok _ => throwError "SVM silently discarded NEAR entry metadata"
  let privateView ←
    match IR.fromExtracted privateViewSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let secret ← match privateView.entries.find? (·.ixName == "secret") with
    | some method => pure method
    | none => throwError "missing private view"
  unless secret.entryPolicy == "near.entry.v1:private" do
    throwError "private view lost its entry policy"
  let secretWat ← match Emit.emit privateView with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let secretBody ← match secretWat.splitOn "(func (export \"secret\")" with
    | [_preamble, body] => pure body
    | _ => throwError "private view WAT must contain exactly one exported body"
  unless secretBody.contains "(call $pf_current_account_id" &&
      secretBody.contains "(call $pf_predecessor_account_id" &&
      !secretBody.contains "(call $pf_attached_deposit" do
    throwError "private view wrapper imports or guard policy are wrong"
  match ProofForge.Extract.extractModuleIR env `Tests.NearPromiseSpec.PayableView >>=
      IR.fromExtracted with
  | .error reason =>
      unless reason.contains "view cannot be payable" do
        throwError s!"wrong payable-view rejection: {reason}"
  | .ok _ => throwError "NEAR admitted a payable view"
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearPromise with
    | .ok program => pure program
    | .error reason => throwError reason
  let sourceRecordValue ← match source.methods.find? (·.ixName == "recordValue") with
    | some method => pure method
    | none => throwError "missing extracted recordValue method"
  unless sourceRecordValue.annotations == #["near.payable.v1"] do
    throwError "extractor lost NEAR payable metadata"
  for name in #["callbackSuccess", "callbackFailure", "callbackOversized", "callbackJoined"] do
    let callback ← match source.methods.find? (·.ixName == name) with
      | some method => pure method
      | none => throwError s!"missing extracted {name} callback"
    unless callback.annotations == #["near.private.v1"] do
      throwError s!"extractor lost NEAR private metadata on {name}"
  let steps := source.methods.foldl (init := #[]) fun acc method => acc ++ promiseSteps method.ops
  let detachedRecord := "detached.receiver.test.near.record.8.9"
  let detachedMissing := "detached.receiver.test.near.missing.8.9"
  let returnedRecord := "returned.receiver.test.near.recordValue.8.9"
  let returnedMissing := "returned.receiver.test.near.missing.8.9"
  let thenSuccess := "then.receiver.test.near.recordValue.callbackSuccess.8.8.9.9"
  let thenFailure := "then.receiver.test.near.missing.callbackFailure.8.8.9.9"
  let thenOversized := "then.receiver.test.near.recordValue.callbackOversized.8.8.9.9"
  let andSuccess :=
    "and.receiver.test.near.echo.receiver.test.near.echo.callbackJoined.8.8.8.9.9.9"
  let andRightMissing :=
    "and.receiver.test.near.echo.receiver.test.near.missing.callbackJoined.8.8.8.9.9.9"
  let andLeftMissing :=
    "and.receiver.test.near.missing.receiver.test.near.echo.callbackJoined.8.8.8.9.9.9"
  let transferDetached := "transfer.detached.receiver.test.near"
  let transferReturned := "transfer.returned.receiver.test.near"
  unless steps.size == 16 && (steps.filter (· == detachedRecord)).size == 4 &&
      (steps.filter (· == detachedMissing)).size == 1 &&
      (steps.filter (· == returnedRecord)).size == 1 &&
      (steps.filter (· == returnedMissing)).size == 1 &&
      (steps.filter (· == thenSuccess)).size == 1 &&
      (steps.filter (· == thenFailure)).size == 1 &&
      (steps.filter (· == thenOversized)).size == 1 &&
      (steps.filter (· == andSuccess)).size == 1 &&
      (steps.filter (· == andRightMissing)).size == 1 &&
      (steps.filter (· == andLeftMissing)).size == 1 &&
      (steps.filter (· == transferDetached)).size == 2 &&
      (steps.filter (· == transferReturned)).size == 1 do
    throwError s!"extractor lost or duplicated promise effects: {repr steps}"
  let decodes := source.methods.foldl (init := #[]) fun acc method =>
    acc ++ resultDecodes method.ops
  unless decodes.size == 5 && (decodes.filter (· == 8)).size == 4 &&
      (decodes.filter (· == 4)).size == 1 do
    throwError s!"extractor lost strict callback UInt64 decoders: {repr decodes}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let recordValue ← match program.entries.find? (·.ixName == "recordValue") with
    | some method => pure method
    | none => throwError "missing lowered recordValue method"
  unless recordValue.entryPolicy == "near.entry.v1:payable" do
    throwError "NEAR IR lost canonical payable entry policy"
  for name in #["callbackSuccess", "callbackFailure", "callbackOversized", "callbackJoined"] do
    let callback ← match program.entries.find? (·.ixName == name) with
      | some method => pure method
      | none => throwError s!"missing lowered {name} callback"
    unless callback.entryPolicy == "near.entry.v1:private" do
      throwError s!"NEAR IR lost canonical private entry policy on {name}"
  let recordValueWat ← match Emit.emit { program with entries := #[recordValue] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let recordValueBody ← match recordValueWat.splitOn "(func (export \"recordValue\")" with
    | [_preamble, body] => pure body
    | _ => throwError "recordValue WAT must contain exactly one exported body"
  unless !recordValueBody.contains "(call $pf_attached_deposit" do
    throwError "donation-only payable recordValue retained a non-payable guard"
  match Emit.emit { program with initializer :=
      { program.initializer with entryPolicy := "near.entry.v9:unknown" } } with
  | .error reason =>
      unless reason.contains "malformed near entry policy" do
        throwError s!"wrong malformed entry-policy rejection: {reason}"
  | .ok _ => throwError "emitter accepted malformed NEAR entry policy"
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
  if sendWat.contains "promise_and" then
    throwError "plain detached Promise method unexpectedly retained promise_and"
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
  let transferDetachedMethod ← match program.entries.find? (·.ixName == "transferDetached") with
    | some method => pure method
    | none => throwError "missing transferDetached entry"
  let transferDetachedWat ←
    match Emit.emit { program with entries := #[transferDetachedMethod] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(import \"env\" \"promise_batch_create\"",
      "(import \"env\" \"promise_batch_action_transfer\" " ++
        "(func $pf_promise_batch_action_transfer (param i64 i64)))",
      "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
      "(i64.store (i32.wrap_i64 (local.get $pf_r0)) (i64.const 7))",
      "(i64.store (i32.add (i32.wrap_i64 (local.get $pf_r0)) (i32.const 8)) (i64.const 1))",
      "(call $pf_promise_batch_action_transfer (local.get $pf_r1) (local.get $pf_r0))" ] do
    unless transferDetachedWat.contains anchor do
      throwError s!"detached transfer WAT missing {anchor}\n{transferDetachedWat}"
  if transferDetachedWat.contains "promise_batch_action_function_call" ||
      transferDetachedWat.contains "promise_return" then
    throwError "detached transfer retained function-call or returned-Promise imports"
  match transferDetachedWat.splitOn "(call $pf_promise_batch_create" with
  | [_beforeCreate, afterCreate] =>
      unless afterCreate.contains "(call $pf_promise_batch_action_transfer" do
        throwError "detached transfer action was appended before its batch was created"
  | _ => throwError "detached transfer must create exactly one Promise batch"
  let transferReturnedMethod ← match program.entries.find? (·.ixName == "transferReturned") with
    | some method => pure method
    | none => throwError "missing transferReturned entry"
  let transferReturnedWat ←
    match Emit.emit { program with entries := #[transferReturnedMethod] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(i64.store (i32.wrap_i64 (local.get $pf_r0)) (i64.const 11))",
      "(i64.store (i32.add (i32.wrap_i64 (local.get $pf_r0)) (i32.const 8)) (i64.const 0))",
      "(call $pf_promise_batch_action_transfer (local.get $pf_r1) (local.get $pf_r0))" ] do
    unless transferReturnedWat.contains anchor do
      throwError s!"returned transfer WAT missing {anchor}\n{transferReturnedWat}"
  match transferReturnedWat.splitOn "(call $pf_promise_batch_action_transfer" with
  | [_beforeAction, afterAction] =>
      match afterAction.splitOn "(call $pf_promise_return" with
      | [between, _afterReturn] =>
          unless between.contains "(call $pf_storage_write" do
            throwError "returned transfer was linked before caller-state persistence"
      | _ => throwError "returned transfer must call promise_return exactly once"
  | _ => throwError "returned transfer must append exactly one transfer action"
  if transferReturnedWat.contains "promise_batch_action_function_call" ||
      transferReturnedWat.contains "(call $pf_value_return" then
    throwError "returned transfer retained a function-call action or overwrote promise_return"
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
  let sendAndSuccess ← match program.entries.find? (·.ixName == "sendAndSuccess") with
    | some method => pure method
    | none => throwError "missing sendAndSuccess entry"
  let andWat ← match Emit.emit { program with entries := #[sendAndSuccess] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(import \"env\" \"promise_and\" " ++
        "(func $pf_promise_and (param i64 i64) (result i64)))",
      "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
      "(local.set $pf_r8 (i64.extend_i32_u " ++
        "(call $pf_arena_alloc (i64.const 16) (i64.const 8))))",
      "(i64.store (i32.wrap_i64 (local.get $pf_r8)) (local.get $pf_r3))",
      "(i64.store (i32.add (i32.wrap_i64 (local.get $pf_r8)) " ++
        "(i32.const 8)) (local.get $pf_r7))",
      "(local.set $pf_r9 (call $pf_promise_and (local.get $pf_r8) (i64.const 2)))",
      "(call $pf_promise_batch_then (local.get $pf_r9)",
      "(call $pf_promise_return (local.get $pf_r13))" ] do
    unless andWat.contains anchor do
      throwError s!"joined Promise WAT missing {anchor}\n{andWat}"
  match andWat.splitOn "(call $pf_promise_and" with
  | [beforeAnd, afterAnd] =>
      unless (beforeAnd.splitOn "(call $pf_promise_batch_create").length == 3 &&
          (beforeAnd.splitOn "(call $pf_promise_batch_action_function_call").length == 3 do
        throwError "promise_and must follow exactly two created child function-call actions"
      unless (beforeAnd.splitOn "(i64.store").length ≥ 7 do
        throwError "promise_and input indices were not stored after both child deposit frames"
      match afterAnd.splitOn "(call $pf_promise_batch_then" with
      | [_joinTail, afterThen] =>
          match afterThen.splitOn "(call $pf_promise_batch_action_function_call" with
          | [_thenTail, afterCallbackAction] =>
              match afterCallbackAction.splitOn "(call $pf_promise_return" with
              | [beforeReturn, _afterReturn] =>
                  unless beforeReturn.contains "(call $pf_storage_write" do
                    throwError "joined callback was returned before caller-state persistence"
              | _ => throwError "joined callback must call promise_return exactly once"
          | _ => throwError "joined callback must append exactly one action after batch_then"
      | _ => throwError "joined Promise must feed exactly one promise_batch_then dependency"
  | _ => throwError "joined Promise method must call promise_and exactly once"
  unless (andWat.splitOn "(call $pf_promise_batch_action_function_call").length == 4 do
    throwError "joined Promise method must append exactly three function-call actions"
  if andWat.contains "promise_batch_action_transfer" ||
      andWat.contains "(call $pf_value_return" then
    throwError "joined Promise retained transfer action or overwrote promise_return"
  let callbackSuccess ← match program.entries.find? (·.ixName == "callbackSuccess") with
    | some method => pure method
    | none => throwError "missing callbackSuccess entry"
  let callbackSuccessWat ← match Emit.emit { program with entries := #[callbackSuccess] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(import \"env\" \"predecessor_account_id\"",
      "(import \"env\" \"current_account_id\"",
      "(i64.eq (local.get $pf_self_len) (local.get $pf_pred_len))",
      "(i64.eq (local.get $pf_self) (local.get $pf_pred))",
      "(i64.eq (local.get $pf_self1) (local.get $pf_pred1))",
      "(i64.eq (local.get $pf_self2) (local.get $pf_pred2))",
      "(i64.eq (local.get $pf_self3) (local.get $pf_pred3))",
      "(i64.eq (local.get $pf_self4) (local.get $pf_pred4))",
      "(i64.eq (local.get $pf_self5) (local.get $pf_pred5))",
      "(i64.eq (local.get $pf_self6) (local.get $pf_pred6))",
      "(i64.eq (local.get $pf_self7) (local.get $pf_pred7))",
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
  let afterCurrent ← match callbackBody.splitOn "(call $pf_current_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackSuccess must read current account exactly once"
  let afterPredecessor ← match afterCurrent.splitOn "(call $pf_predecessor_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackSuccess must read predecessor after current account"
  let afterPrivate ← match afterPredecessor.splitOn
      "(call $pf_panic_utf8 (i64.const 33)" with
    | [before, after] =>
        if before.contains "(call $pf_attached_deposit" || before.contains "(call $pf_input" ||
            before.contains "(call $pf_promise_result" then
          throwError "private guard did not precede deposit, input, and callback-result handling"
        pure after
    | _ => throwError "callbackSuccess must emit one exact private panic"
  let afterDeposit ← match afterPrivate.splitOn "(call $pf_attached_deposit" with
    | [before, after] =>
        unless !before.contains "(call $pf_input" do
          throwError "callback input was decoded before its non-payable guard"
        pure after
    | _ => throwError "private callback must retain one non-payable guard"
  match afterDeposit.splitOn "(call $pf_promise_result (i64.const 0)" with
  | [beforeRead, _afterRead] =>
      unless beforeRead.contains "(call $pf_input" do
        throwError "callback result was read before ordinary input decoding"
      unless beforeRead.contains
          "(call $pf_storage_has_key (i64.const 5) (i64.const 2096)) (i64.const 0)" do
        throwError "callback result was read before the missing-STATE guard"
  | _ => throwError "callbackSuccess must read its Promise result exactly once after guards"
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
  let callbackJoined ← match program.entries.find? (·.ixName == "callbackJoined") with
    | some method => pure method
    | none => throwError "missing callbackJoined entry"
  let callbackJoinedWat ← match Emit.emit { program with entries := #[callbackJoined] } with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(call $pf_promise_results_count)",
      "(call $pf_promise_result (i64.const 0)",
      "(call $pf_promise_result (i64.const 1)",
      "(else (i64.const 999))",
      "(local.set $depositLo (local.get $pf_v0))",
      "(local.set $depositHi (local.get $pf_v1))",
      "(i64.const 2)" ] do
    unless callbackJoinedWat.contains anchor do
      throwError s!"joined callback WAT missing {anchor}\n{callbackJoinedWat}"
  let joinedBody ← match callbackJoinedWat.splitOn "(func (export \"callbackJoined\")" with
    | [_preamble, body] => pure body
    | _ => throwError "callbackJoined WAT must contain exactly one exported body"
  let afterJoinedCurrent ← match joinedBody.splitOn "(call $pf_current_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackJoined must read current account exactly once"
  let afterJoinedPredecessor ← match afterJoinedCurrent.splitOn
      "(call $pf_predecessor_account_id" with
    | [_before, after] => pure after
    | _ => throwError "callbackJoined must read predecessor after current account"
  match afterJoinedPredecessor.splitOn "(call $pf_promise_result (i64.const 0)" with
  | [beforeLeft, afterLeft] =>
      unless beforeLeft.contains
          "(call $pf_storage_has_key (i64.const 5) (i64.const 2096)) (i64.const 0)" do
        throwError "joined callback read dependency results before the missing-STATE guard"
      match afterLeft.splitOn "(call $pf_promise_result (i64.const 1)" with
      | [_between, _afterRight] => pure ()
      | _ => throwError "joined callback did not read right result exactly once after left result"
  | _ => throwError "joined callback did not read left result exactly once after identity loads"
  for (name, callbackWat) in #[
      ("callbackFailure", callbackFailureWat),
      ("callbackOversized", callbackOversizedWat) ] do
    for anchor in #[
        "(call $pf_current_account_id",
        "(call $pf_predecessor_account_id",
        "(i64.eq (local.get $pf_self_len) (local.get $pf_pred_len))",
        "(i64.eq (local.get $pf_self) (local.get $pf_pred))",
        "(i64.eq (local.get $pf_self7) (local.get $pf_pred7))",
        "(if (i32.eqz (i32.and" ] do
      unless callbackWat.contains anchor do
        throwError s!"{name} lost private self-call guard anchor {anchor}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"promise_batch_create\"",
    "(import \"env\" \"promise_batch_action_function_call\"",
    "(import \"env\" \"promise_batch_action_transfer\"",
    "(import \"env\" \"promise_return\"",
    "(func (export \"send\")",
    "(func (export \"sendMissing\")",
    "(func (export \"sendReturned\")",
    "(func (export \"sendReturnedMissing\")",
    "(func (export \"sendThenSuccess\")",
    "(func (export \"sendThenMissing\")",
    "(func (export \"sendThenOversized\")",
    "(func (export \"transferDetached\")",
    "(func (export \"transferReturned\")",
    "(func (export \"transferTooMuch\")",
    "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
    "(i64.store (i32.wrap_i64",
    "(i32.const 8))",
    "(call $pf_promise_batch_create (i64.const 18) (i64.const 8192))",
    "(call $pf_promise_batch_action_function_call",
    "(call $pf_promise_batch_then",
    "(call $pf_promise_return",
    "(i64.const 6) (i64.const 8210)",
    "(i64.const 7) (i64.const 8216)",
    "(i64.const 11) (i64.const 8241)",
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
  let viewTransferDetached := { source with methods := source.methods.map fun method =>
    if method.ixName == "transferDetached" then { method with kind := .get } else method }
  match IR.fromExtracted viewTransferDetached >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong detached-transfer view rejection: {reason}"
  | .ok _ => throwError "detached transfer was accepted in a view"
  let viewTransferReturned := { source with methods := source.methods.map fun method =>
    if method.ixName == "transferReturned" then { method with kind := .get } else method }
  match IR.fromExtracted viewTransferReturned >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong returned-transfer view rejection: {reason}"
  | .ok _ => throwError "returned transfer was accepted in a view"
  let viewThen := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendThenSuccess" then { method with kind := .get } else method }
  match IR.fromExtracted viewThen >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong callback-view rejection: {reason}"
  | .ok _ => throwError "callback Promise chain was accepted in a view"
  let viewAnd := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendAndSuccess" then { method with kind := .get } else method }
  match IR.fromExtracted viewAnd >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong joined-Promise view rejection: {reason}"
  | .ok _ => throwError "joined Promise chain was accepted in a view"
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
  let returnedTransferOp ←
    match source.methods.find? (·.ixName == "transferReturned") with
    | some method =>
        match method.ops.find? fun op =>
          match op with
          | .ext (.near (.promiseTransferReturned _ _ _)) => true
          | _ => false with
        | some op => pure op
        | none => throwError "missing returned-transfer effect"
    | none => throwError "missing extracted transferReturned method"
  let mixedReturned := { source with methods := source.methods.map fun method =>
    if method.ixName == "sendReturned" then
      { method with ops := method.ops.flatMap fun op =>
          match op with
          | .ext (.near (.promiseFunctionCallReturned _ _ _ _ _ _ _)) =>
              #[op, returnedTransferOp]
          | _ => #[op] }
    else method }
  match IR.fromExtracted mixedReturned >>= Emit.emit with
  | .error reason =>
      unless reason.contains "cannot return more than one promise" do
        throwError s!"wrong mixed-returned-Promise rejection: {reason}"
  | .ok _ => throwError "returned call plus returned transfer was accepted on one path"
  logInfo m!"proofforge-near-promise: digest = {IR.digestHex program}"

#pf_near_promise_check

end Tests.NearPromiseSpec
