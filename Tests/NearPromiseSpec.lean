import Examples.NearPromise
import Lean
import ProofForge

/-! Static detached Promise extraction, projection, and WAT invariants. -/

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
          #[s!"{receiver}.{method}.{capacity}.{arguments.size}"]
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
  let record := "receiver.test.near.record.8.9"
  let missing := "receiver.test.near.missing.8.9"
  unless steps.size == 5 && (steps.filter (· == record)).size == 4 &&
      (steps.filter (· == missing)).size == 1 do
    throwError s!"extractor lost or duplicated detached promise effects: {repr steps}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  for method in program.entries do
    match Emit.emit { program with entries := #[method] } with
    | .ok _ => pure ()
    | .error reason => throwError s!"{method.ixName}: {reason}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"promise_batch_create\"",
    "(import \"env\" \"promise_batch_action_function_call\"",
    "(func (export \"send\")",
    "(func (export \"sendMissing\")",
    "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
    "(i64.store (i32.wrap_i64",
    "(i32.const 8))",
    "(call $pf_promise_batch_create (i64.const 18) (i64.const 8192))",
    "(call $pf_promise_batch_action_function_call",
    "(i64.const 6) (i64.const 8210)",
    "(i64.const 7) (i64.const 8216)",
    "(i64.const 20000000000000)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR detached Promise WAT missing {anchor}\n{wat}"
  if wat.contains "promise_return" then
    throwError "detached Promise slice unexpectedly imports or calls promise_return"
  let viewCall := { source with methods := source.methods.map fun method =>
    if method.ixName == "send" then { method with kind := .get } else method }
  match IR.fromExtracted viewCall >>= Emit.emit with
  | .error reason =>
      unless reason.contains "view cannot create a promise" do
        throwError s!"wrong view-promise rejection: {reason}"
  | .ok _ => throwError "detached Promise call was accepted in a view"
  logInfo m!"proofforge-near-promise: digest = {IR.digestHex program}"

#pf_near_promise_check

end Tests.NearPromiseSpec
