import Examples.NearFungibleLedger
import Lean
import ProofForge

/-! Closed AccountId/NearToken fungible-ledger extraction and WAT invariants. -/

namespace Tests.NearFungibleLedgerSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key value _ _)) =>
          #[s!"write.{result}.{key}.{value}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

elab "#pf_near_fungible_ledger_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearFungibleLedger with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "mintSelfOne" == #["read.16.72", "write.16.72.16"] &&
      methodSteps "ft_balance_of" == #["read.16.72"] &&
      methodSteps "ft_total_supply" == #[] &&
      methodSteps "ft_transfer" ==
        #["read.16.72", "read.16.72", "write.16.72.16", "write.16.72.16"] &&
      methodSteps "burnSelfOne" ==
        #["read.16.72", "remove.16.72", "write.16.72.16"] &&
      methodSteps "transferCallerToSelfOne" ==
        #["read.16.72", "read.16.72", "remove.16.72", "write.16.72.16",
          "write.16.72.16", "write.16.72.16"] &&
      methodSteps "seedSelfMalformed8" == #["write.16.72.20"] &&
      methodSteps "seedSelfMalformed20" == #["write.16.72.20"] do
    throwError s!"fungible ledger effects lost prerequisite reads or write-last branches: " ++
      s!"mint={methodSteps "mintSelfOne"}, burn={methodSteps "burnSelfOne"}, " ++
      s!"balance={methodSteps "ft_balance_of"}, " ++
      s!"ft_transfer={methodSteps "ft_transfer"}, " ++
      s!"transfer={methodSteps "transferCallerToSelfOne"}, " ++
      s!"malformed8={methodSteps "seedSelfMalformed8"}, " ++
      s!"malformed20={methodSteps "seedSelfMalformed20"}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some balance := program.entries.find? (·.ixName == "ft_balance_of")
    | throwError "missing target ft_balance_of"
  unless balance.inputSchema == some Codec.accountIdSchema &&
      balance.inputPolicy ==
        "near-json-account-id-object-bounded-v1(max-wire=433,ws=32,keys=canonical,unknown=reject)" &&
      balance.outputSchema == some (.scalar .uint128) &&
      balance.outputPolicy == "near-json-u128-string-v1" && balance.paramCount == 9 &&
      balance.tupleArity == some 2 do
    throwError "ft_balance_of lost its specialized AccountId-input/u128-output composition"
  let some supply := program.entries.find? (·.ixName == "ft_total_supply")
    | throwError "missing target ft_total_supply"
  unless supply.inputSchema.isNone && supply.inputPolicy.isEmpty &&
      supply.outputSchema == some (.scalar .uint128) &&
      supply.outputPolicy == "near-json-u128-string-v1" && supply.paramCount == 0 &&
      supply.tupleArity == some 2 do
    throwError "ft_total_supply lost its no-input quoted-u128 view policy"
  let some transfer := program.entries.find? (·.ixName == "ft_transfer")
    | throwError "missing target ft_transfer"
  unless transfer.kind == .increment && transfer.entryPolicy == "near.entry.v1:payable" &&
      transfer.inputSchema == some Codec.ftTransferArgsSchema &&
      transfer.inputPolicy ==
        "near-json-ft-transfer-args-bounded-v1(max-wire=786,ws=32,order=any,keys=raw,unknown=reject)" &&
      transfer.outputSchema == some .unit && transfer.outputPolicy == "near-void-empty-v1" &&
      transfer.paramCount == 15 && transfer.tupleArity.isNone do
    throwError "ft_transfer lost payable bounded-input or empty-output target policy"
  let some resolver := program.entries.find? (·.ixName == "ft_resolve_transfer")
    | throwError "missing target ft_resolve_transfer"
  unless resolver.kind == .increment && resolver.entryPolicy == "near.entry.v1:private" &&
      resolver.inputSchema == some Codec.ftResolveTransferArgsSchema &&
      resolver.inputPolicy ==
        "near-json-ft-resolve-args-bounded-v1(max-wire=1079,ws=32,order=any,keys=raw,unknown=reject)" &&
      resolver.outputSchema == some (.scalar .uint128) &&
      resolver.outputPolicy == "near-json-u128-string-v1" && resolver.paramCount == 20 &&
      resolver.tupleArity == some 2 do
    throwError "ft_resolve_transfer lost private bounded-input or quoted-u128 output policy"
  for method in program.entries do
    match Emit.emit { program with entries := #[method] } with
    | .ok _ => pure ()
    | .error reason => throwError s!"{method.ixName}: {reason}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"mintSelfOne\")", "(func (export \"mintSelfTwo64\")",
      "(func (export \"mintSelfMax\")", "(func (export \"burnSelfOne\")",
      "(func (export \"transferCallerToSelfOne\")",
      "(func (export \"transferCallerToSelfZero\")",
      "(func (export \"ft_balance_of\")",
      "(func (export \"ft_total_supply\")",
      "(func (export \"ft_transfer\")",
      "(func (export \"seedSelfMalformed8\")",
      "(func (export \"fixtureSetSupplyMax\")",
      "(call $pf_storage_read", "(call $pf_storage_write", "(call $pf_storage_remove",
      "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
      "(func $pf_json_account_id", "(func $pf_u128_decimal",
      "i64.add", "i64.sub", "i64.lt_u", "i64.ge_u", "i64.and", "i64.or"] do
    unless wat.contains anchor do
      throwError s!"NEAR fungible ledger WAT missing {anchor}\n{wat}"
  let fixtureBody ← match wat.splitOn "(func (export \"fixtureSetSupplyMax\")" with
    | [_before, tail] =>
        match tail.splitOn "\n  )\n" with
        | body :: _ => pure body
        | [] => throwError "fixtureSetSupplyMax body terminator is missing"
    | _ => throwError "fixtureSetSupplyMax body must occur exactly once"
  unless (fixtureBody.splitOn
      "(call $pf_storage_write (i64.const 8) (i64.const 1024)").length == 2 &&
      (fixtureBody.splitOn
        "(call $pf_storage_write (i64.const 8) (i64.const 1032)").length == 2 &&
      (fixtureBody.splitOn
        "(call $pf_storage_write (i64.const 6) (i64.const 1040)").length == 2 do
    throwError "fixtureSetSupplyMax did not persist each supply/marker field exactly once"
  let balanceBody ← match wat.splitOn "(func (export \"ft_balance_of\")" with
    | [_before, tail] =>
        match tail.splitOn "\n  )\n" with
        | body :: _ => pure body
        | [] => throwError "ft_balance_of body terminator is missing"
    | _ => throwError "ft_balance_of must occur exactly once"
  unless (balanceBody.splitOn "(call $pf_input").length == 2 &&
      (balanceBody.splitOn "(call $pf_value_return").length == 2 &&
      !balanceBody.contains "(call $pf_storage_write" &&
      !balanceBody.contains "(call $pf_storage_remove" &&
      !balanceBody.contains "(call $pf_log_utf8" &&
      !balanceBody.contains "(call $pf_promise" do
    throwError "ft_balance_of must read/value_return once without writes, logs, or promises"
  let supplyBody ← match wat.splitOn "(func (export \"ft_total_supply\")" with
    | [_before, tail] =>
        match tail.splitOn "\n  )\n" with
        | body :: _ => pure body
        | [] => throwError "ft_total_supply body terminator is missing"
    | _ => throwError "ft_total_supply must occur exactly once"
  unless (supplyBody.splitOn "(call $pf_input").length == 2 &&
      (supplyBody.splitOn "(call $pf_value_return").length == 2 &&
      !supplyBody.contains "(call $pf_storage_write" &&
      !supplyBody.contains "(call $pf_storage_remove" &&
      !supplyBody.contains "(call $pf_log_utf8" &&
      !supplyBody.contains "(call $pf_promise" do
    throwError "ft_total_supply must enforce empty input and value_return once without effects"
  let transferBody ← match wat.splitOn "(func (export \"ft_transfer\")" with
    | [_before, tail] =>
        match tail.splitOn "\n  )\n" with
        | body :: _ => pure body
        | [] => throwError "ft_transfer body terminator is missing"
    | _ => throwError "ft_transfer must occur exactly once"
  let mapWrites := transferBody.splitOn
    "(global.set $pf_storage_result_status (call $pf_storage_write"
  let depositParts := transferBody.splitOn "(call $pf_attached_deposit"
  unless (transferBody.splitOn "(call $pf_input").length == 2 &&
      depositParts.length == 2 &&
      !depositParts[0]!.contains "(global.set $pf_storage_result_status" &&
      depositParts[1]!.contains
        "(global.set $pf_storage_result_status (call $pf_storage_read" &&
      (transferBody.splitOn
        "(global.set $pf_storage_result_status (call $pf_storage_read").length == 3 &&
      mapWrites.length == 3 && !mapWrites[1]!.contains "(call $pf_log_utf8" &&
      mapWrites[2]!.contains "(call $pf_log_utf8" &&
      !transferBody.contains "(call $pf_storage_remove" &&
      !transferBody.contains "(call $pf_value_return" do
    throwError "ft_transfer lost guard/read/read/write/write/event/empty-return ordering"
  let resolverBody ← match wat.splitOn "(func (export \"ft_resolve_transfer\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "ft_resolve_transfer must occur exactly once"
  let afterCurrent ← match resolverBody.splitOn "(call $pf_current_account_id" with
    | [_before, after] => pure after
    | _ => throwError "ft_resolve_transfer must read current account exactly once"
  let afterPredecessor ← match afterCurrent.splitOn "(call $pf_predecessor_account_id" with
    | [_before, after] => pure after
    | _ => throwError "ft_resolve_transfer must read predecessor after current account"
  let afterPrivate ← match afterPredecessor.splitOn
      "(call $pf_panic_utf8 (i64.const 37)" with
    | [before, after] =>
        unless !before.contains "(call $pf_attached_deposit" &&
            !before.contains "(call $pf_input" do
          throwError "resolver private guard did not precede deposit and input handling"
        pure after
    | _ => throwError "ft_resolve_transfer lost its private guard"
  let afterDeposit ← match afterPrivate.splitOn "(call $pf_attached_deposit" with
    | [before, after] =>
        unless !before.contains "(call $pf_input" &&
            after.contains "(i64.load (i32.const 24))" &&
            after.contains "(i64.load (i32.const 32))" do
          throwError "resolver non-payable guard order or full-u128 check changed"
        pure after
    | _ => throwError "ft_resolve_transfer must enforce non-payable exactly once"
  let afterCount ← match afterDeposit.splitOn "(call $pf_promise_results_count" with
    | [before, after] =>
        unless before.contains "(call $pf_input" &&
            !before.contains "(global.set $pf_storage_result_status (call $pf_storage_write" do
          throwError "resolver result count did not precede ledger writes"
        pure after
    | _ => throwError "resolver must inspect Promise result count exactly once"
  let afterResult ← match afterCount.splitOn "(call $pf_promise_result (i64.const 0)" with
    | [before, after] =>
        unless !before.contains "(global.set $pf_storage_result_status (call $pf_storage_write" do
          throwError "resolver decoded its Promise result after a ledger write"
        pure after
    | _ => throwError "resolver must read Promise result index zero exactly once"
  unless (afterResult.splitOn
        "(global.set $pf_storage_result_status (call $pf_storage_read").length == 3 &&
      (resolverBody.splitOn
        "(global.set $pf_storage_result_status (call $pf_storage_write").length == 4 &&
      (resolverBody.splitOn "(call $pf_log_utf8").length == 3 &&
      (resolverBody.splitOn "(call $pf_value_return").length == 4 &&
      !resolverBody.contains "(call $pf_storage_remove" &&
      !resolverBody.contains "(call $pf_value_return (i64.const 8)" do
    throwError "resolver lost read-before-write, one-event, present-zero, or quoted-output branches"
  logInfo m!"proofforge-near-fungible-ledger: digest = {IR.digestHex program}"

#pf_near_fungible_ledger_check

#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleLedger" ==
  some "9a4d88d130820c6b"

end Tests.NearFungibleLedgerSpec
