import Examples.Near.NearFtReceiverDual
import Lean
import ProofForge

namespace Tests.NearFtReceiverDualSpec

open Lean Elab Command
open ProofForge.Wasm.Near

elab "#pf_near_ft_receiver_dual_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.Near.NearFtReceiverDual with
    | .ok program => pure program | .error reason => throwError reason
  let some sourceReceiver := source.methods.find? (·.ixName == "ft_on_transfer")
    | throwError "missing source ft_on_transfer"
  unless sourceReceiver.kind == .increment && sourceReceiver.paramSchemas == #[Codec.ftOnTransferArgsSchema] &&
      sourceReceiver.retSchema == .scalar .uint128 && sourceReceiver.retCount == 2 &&
      sourceReceiver.annotations.contains "near.promise-or-value-u128.v1" do
    throwError "extractor lost exact receiver dual boundary"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let some receiver := program.entries.find? (·.ixName == "ft_on_transfer")
    | throwError "missing target ft_on_transfer"
  unless receiver.entryPolicy.isEmpty && receiver.inputSchema == some Codec.ftOnTransferArgsSchema &&
      receiver.outputSchema == some (.scalar .uint128) &&
      receiver.outputPolicy == "near-promise-or-json-u128-v1" && receiver.paramCount == 20 do
    throwError "target lost nonpayable bounded-input dual-output receiver policy"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  let parts := wat.splitOn "(func (export \"ft_on_transfer\")"
  unless parts.length == 2 do throwError "ft_on_transfer must be exported exactly once"
  let body := (parts[1]!).splitOn "\n  (func (export" |>.head!
  unless (body.splitOn "(call $pf_value_return").length == 4 &&
      (body.splitOn "(call $pf_promise_return").length == 4 &&
      (body.splitOn "(call $pf_promise_batch_create").length == 4 &&
      (body.splitOn "(drop (call $pf_storage_write").length ≥ 7 &&
      body.contains "(call $pf_panic_utf8" do
    throwError "receiver lost three immediate/three Promise branch terminals or state stores"
  for terminal in #["(call $pf_value_return", "(call $pf_promise_return"] do
    let first := body.splitOn terminal
    unless first.length ≥ 2 && first[0]!.contains "(call $pf_attached_deposit" &&
        first[0]!.contains "(call $pf_json_ft_on_transfer_args" do
      throwError s!"receiver guard/input did not precede {terminal}"
  logInfo m!"proofforge-near-ft-receiver-dual: digest = {IR.digestHex program}"

#pf_near_ft_receiver_dual_check

end Tests.NearFtReceiverDualSpec
