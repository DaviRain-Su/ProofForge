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
  logInfo m!"proofforge-near-fungible-ledger: digest = {IR.digestHex program}"

#pf_near_fungible_ledger_check

#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleLedger" ==
  some "954015ffa13ff1f1"

end Tests.NearFungibleLedgerSpec
