import Examples.NearFtReceiverValue
import Lean
import ProofForge

namespace Tests.NearFtReceiverValueSpec

open Lean Elab Command
open ProofForge.Wasm.Near

elab "#pf_near_ft_receiver_value_check" : command => do
  let env ← getEnv
  let source ← match ProofForge.Extract.extractModuleIR env `Examples.NearFtReceiverValue with
    | .ok program => pure program | .error reason => throwError reason
  let some sourceReceiver := source.methods.find? (·.ixName == "ft_on_transfer")
    | throwError "missing source ft_on_transfer"
  unless sourceReceiver.kind == .increment && sourceReceiver.paramCount == 1 &&
      sourceReceiver.paramSchemas == #[Codec.ftOnTransferArgsSchema] &&
      sourceReceiver.retSchema == .scalar .uint128 && sourceReceiver.retCount == 2 do
    throwError m!"extractor lost receiver input or immediate u128 result frame: " ++
      m!"kind={repr sourceReceiver.kind}, params={sourceReceiver.paramCount}/{repr sourceReceiver.paramSchemas}, " ++
      m!"ret={repr sourceReceiver.retSchema}/{sourceReceiver.retCount}"
  let program ← match IR.fromExtracted source with
    | .ok program => pure program | .error reason => throwError reason
  let some receiver := program.entries.find? (·.ixName == "ft_on_transfer")
    | throwError "missing target ft_on_transfer"
  unless receiver.kind == .increment && receiver.entryPolicy.isEmpty &&
      receiver.inputSchema == some Codec.ftOnTransferArgsSchema &&
      receiver.inputPolicy ==
        "near-json-ft-on-transfer-args-bounded-v1(max-wire=1071,ws=32,order=any,keys=raw,unknown=reject)" &&
      receiver.outputSchema == some (.scalar .uint128) &&
      receiver.outputPolicy == "near-json-u128-string-v1" && receiver.paramCount == 20 &&
      receiver.tupleArity == some 2 do
    throwError s!"ft_on_transfer metadata: kind={repr receiver.kind}, entry={receiver.entryPolicy}, " ++
      s!"input={repr receiver.inputSchema}/{receiver.inputPolicy}, output=" ++
      s!"{repr receiver.outputSchema}/{receiver.outputPolicy}, params={receiver.paramCount}, " ++
      s!"tuple={repr receiver.tupleArity}"
  let wat ← match Emit.emit program with
    | .ok wat => pure wat | .error reason => throwError reason
  for anchor in #["(func (export \"ft_on_transfer\")", "(func $pf_json_ft_on_transfer_args",
      "(func $pf_u128_decimal", "(i64.const 1071)", "(call $pf_attached_deposit",
      "(call $pf_storage_write", "(call $pf_value_return"] do
    unless wat.contains anchor do throwError s!"receiver-value WAT missing {anchor}"
  let parts := wat.splitOn "(func (export \"ft_on_transfer\")"
  unless parts.length == 2 do throwError "ft_on_transfer must be exported exactly once"
  let body := (parts[1]!).splitOn "\n  (func (export" |>.head!
  let afterDeposit := body.splitOn "(call $pf_attached_deposit"
  let writes := body.splitOn "(drop (call $pf_storage_write"
  unless afterDeposit.length == 2 &&
      !afterDeposit[0]!.contains "(call $pf_input" && writes.length == 2 &&
      writes[1]!.contains "(call $pf_value_return" &&
      (body.splitOn "(call $pf_value_return").length == 2 &&
      !body.contains "(call $pf_promise_return" && !body.contains "(call $pf_log_utf8" do
    throwError "immediate receiver lost deposit-first/input/state/value_return order"
  logInfo m!"proofforge-near-ft-receiver-value: digest = {IR.digestHex program}"

#pf_near_ft_receiver_value_check

end Tests.NearFtReceiverValueSpec
