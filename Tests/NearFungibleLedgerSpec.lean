import Examples.Near.NearFungibleLedger
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
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearFungibleLedger with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "mintSelfOne" == #["read.16.72", "write.16.72.16"] &&
      methodSteps "ft_balance_of" == #["read.16.72"] &&
      methodSteps "storage_balance_of" == #["read.16.72"] &&
      methodSteps "storage_balance_bounds" == #[] &&
      methodSteps "storage_deposit" == #["read.16.72", "write.16.72.16"] &&
      methodSteps "storage_withdraw" == #["read.16.72"] &&
      methodSteps "storage_unregister" == #["read.16.72", "remove.16.72"] &&
      methodSteps "ft_total_supply" == #[] &&
      methodSteps "ft_metadata" == #[] &&
      methodSteps "ft_transfer" ==
        #["read.16.72", "read.16.72", "write.16.72.16", "write.16.72.16"] &&
      methodSteps "ft_transfer_call" ==
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
      s!"ft_transfer_call={methodSteps "ft_transfer_call"}, " ++
      s!"transfer={methodSteps "transferCallerToSelfOne"}, " ++
      s!"malformed8={methodSteps "seedSelfMalformed8"}, " ++
      s!"malformed20={methodSteps "seedSelfMalformed20"}"
  let some sourceSupply := source.methods.find? (·.ixName == "ft_total_supply")
    | throwError "missing source ft_total_supply"
  unless sourceSupply.annotations == #["near.no-args-ignore-input.v1"] do
    throwError "ft_total_supply lost its explicit no-args wrapper annotation"
  let some sourceMetadata := source.methods.find? (·.ixName == "ft_metadata")
    | throwError "missing source ft_metadata"
  unless sourceMetadata.annotations == #["near.no-args-ignore-input.v1"] &&
      sourceMetadata.retSchema == Codec.fungibleTokenMetadataResultSchema &&
      sourceMetadata.retCount == 70 && sourceMetadata.paramCount == 0 do
    throwError "integrated ft_metadata lost no-args or exact nominal 70-leaf source frame"
  let some sourceStorageBalance := source.methods.find? (·.ixName == "storage_balance_of")
    | throwError "missing source storage_balance_of"
  let some sourceStorageBounds := source.methods.find? (·.ixName == "storage_balance_bounds")
    | throwError "missing source storage_balance_bounds"
  unless sourceStorageBalance.paramSchemas == #[Codec.accountIdSchema] &&
      sourceStorageBalance.retSchema == Codec.storageBalanceResultSchema &&
      sourceStorageBalance.retCount == 5 &&
      sourceStorageBounds.annotations == #["near.no-args-ignore-input.v1"] &&
      sourceStorageBounds.paramCount == 0 &&
      sourceStorageBounds.retSchema == Codec.storageBalanceBoundsResultSchema &&
      sourceStorageBounds.retCount == 5 do
    throwError "integrated storage views lost their exact nominal source frames"
  let some sourceStorageDeposit := source.methods.find? (·.ixName == "storage_deposit")
    | throwError "missing source storage_deposit"
  unless sourceStorageDeposit.paramSchemas == #[Codec.storageDepositArgsSchema] &&
      sourceStorageDeposit.retSchema == Codec.storageBalanceResultSchema &&
      sourceStorageDeposit.retCount == 5 do
    throwError "integrated storage_deposit lost its exact source frames"
  let some sourceStorageWithdraw := source.methods.find? (·.ixName == "storage_withdraw")
    | throwError "missing source storage_withdraw"
  unless sourceStorageWithdraw.paramSchemas == #[Codec.storageWithdrawArgsSchema] &&
      sourceStorageWithdraw.retSchema == Codec.storageBalanceResultSchema &&
      sourceStorageWithdraw.retCount == 5 do
    throwError "integrated storage_withdraw lost its exact source frames"
  let some sourceStorageUnregister := source.methods.find? (·.ixName == "storage_unregister")
    | throwError "missing source storage_unregister"
  unless sourceStorageUnregister.paramSchemas == #[Codec.storageUnregisterArgsSchema] &&
      sourceStorageUnregister.retSchema == Codec.jsonBooleanResultSchema &&
      sourceStorageUnregister.retCount == 1 do
    throwError "integrated storage_unregister lost its exact source frames"
  let duplicateNoArgs := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "ft_total_supply" then
      { candidate with annotations := candidate.annotations.push "near.no-args-ignore-input.v1" }
    else candidate }
  match IR.fromExtracted duplicateNoArgs with
  | .error reason =>
      unless reason.contains "duplicate near no-args annotations" do
        throwError s!"wrong duplicate no-args rejection: {reason}"
  | .ok _ => throwError "duplicate no-args annotation was accepted"
  let parameterizedNoArgs := { source with methods := source.methods.map fun candidate =>
    if candidate.ixName == "ft_balance_of" then
      { candidate with annotations := candidate.annotations.push "near.no-args-ignore-input.v1" }
    else candidate }
  match IR.fromExtracted parameterizedNoArgs with
  | .error reason =>
      unless reason.contains "requires an exact zero-parameter non-initializer" do
        throwError s!"wrong parameterized no-args rejection: {reason}"
  | .ok _ => throwError "no-args annotation was accepted on a parameterized method"
  let initializerNoArgs := { source with methods := source.methods.map fun candidate =>
    if candidate.kind == .init then
      { candidate with annotations := candidate.annotations.push "near.no-args-ignore-input.v1" }
    else candidate }
  match IR.fromExtracted initializerNoArgs with
  | .error reason =>
      unless reason.contains "requires an exact zero-parameter non-initializer" do
        throwError s!"wrong initializer no-args rejection: {reason}"
  | .ok _ => throwError "no-args annotation was accepted on an initializer"
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
  unless supply.inputSchema == some .unit &&
      supply.inputPolicy == "near-no-args-ignore-input-v1" &&
      supply.outputSchema == some (.scalar .uint128) &&
      supply.outputPolicy == "near-json-u128-string-v1" && supply.paramCount == 0 &&
      supply.tupleArity == some 2 do
    throwError "ft_total_supply lost its no-input quoted-u128 view policy"
  let some metadata := program.entries.find? (·.ixName == "ft_metadata")
    | throwError "missing target ft_metadata"
  unless metadata.kind == .get && metadata.inputSchema == some .unit &&
      metadata.inputPolicy == "near-no-args-ignore-input-v1" &&
      metadata.outputSchema == some Codec.fungibleTokenMetadataResultSchema &&
      metadata.outputPolicy == Codec.OutputPlan.jsonFungibleTokenMetadata.canonical &&
      metadata.paramCount == 0 && metadata.tupleArity == some 70 do
    throwError "integrated ft_metadata lost bounded metadata/no-args target composition"
  let some storageBalance := program.entries.find? (·.ixName == "storage_balance_of")
    | throwError "missing target storage_balance_of"
  unless storageBalance.inputSchema == some Codec.accountIdSchema &&
      storageBalance.inputPolicy ==
        "near-json-account-id-object-bounded-v1(max-wire=433,ws=32,keys=canonical,unknown=reject)" &&
      storageBalance.outputSchema == some Codec.storageBalanceResultSchema &&
      storageBalance.outputPolicy == "near-json-storage-balance-option-v1" &&
      storageBalance.tupleArity == some 5 do
    throwError "integrated storage_balance_of lost specialized input/output policies"
  let some storageBounds := program.entries.find? (·.ixName == "storage_balance_bounds")
    | throwError "missing target storage_balance_bounds"
  unless storageBounds.inputSchema == some .unit &&
      storageBounds.inputPolicy == "near-no-args-ignore-input-v1" &&
      storageBounds.outputSchema == some Codec.storageBalanceBoundsResultSchema &&
      storageBounds.outputPolicy == "near-json-storage-balance-bounds-v1" &&
      storageBounds.paramCount == 0 && storageBounds.tupleArity == some 5 do
    throwError "integrated storage_balance_bounds lost exact target policies"
  let some storageDeposit := program.entries.find? (·.ixName == "storage_deposit")
    | throwError "missing target storage_deposit"
  unless storageDeposit.inputSchema == some Codec.storageDepositArgsSchema &&
      storageDeposit.inputPolicy ==
        "near-json-storage-deposit-args-bounded-v1(max-wire=459,ws=32,order=any,keys=raw,unknown=reject)" &&
      storageDeposit.outputSchema == some Codec.storageBalanceResultSchema &&
      storageDeposit.outputPolicy == "near-json-storage-balance-option-v1" &&
      storageDeposit.entryPolicy == "near.entry.v1:payable" &&
      storageDeposit.tupleArity == some 5 do
    throwError "integrated storage_deposit lost payable specialized policies"
  let some storageWithdraw := program.entries.find? (·.ixName == "storage_withdraw")
    | throwError "missing target storage_withdraw"
  unless storageWithdraw.inputSchema == some Codec.storageWithdrawArgsSchema &&
      storageWithdraw.inputPolicy ==
        "near-json-storage-withdraw-args-bounded-v1(max-wire=279,ws=32,digits=1..39,keys=raw,unknown=reject)" &&
      storageWithdraw.outputSchema == some Codec.storageBalanceResultSchema &&
      storageWithdraw.outputPolicy == "near-json-storage-balance-option-v1" &&
      storageWithdraw.entryPolicy == "near.entry.v1:payable" &&
      storageWithdraw.tupleArity == some 5 do
    throwError "integrated storage_withdraw lost payable specialized policies"
  let some storageUnregister := program.entries.find? (·.ixName == "storage_unregister")
    | throwError "missing target storage_unregister"
  unless storageUnregister.inputSchema == some Codec.storageUnregisterArgsSchema &&
      storageUnregister.inputPolicy ==
        "near-json-storage-unregister-args-bounded-v1(max-wire=47,ws=32,keys=raw,unknown=reject)" &&
      storageUnregister.outputSchema == some Codec.jsonBooleanResultSchema &&
      storageUnregister.outputPolicy == "near-json-boolean-v1" &&
      storageUnregister.entryPolicy == "near.entry.v1:payable" &&
      storageUnregister.tupleArity == some 1 do
    throwError "integrated storage_unregister lost payable specialized policies"
  let some transfer := program.entries.find? (·.ixName == "ft_transfer")
    | throwError "missing target ft_transfer"
  unless transfer.kind == .increment && transfer.entryPolicy == "near.entry.v1:payable" &&
      transfer.inputSchema == some Codec.ftTransferArgsSchema &&
      transfer.inputPolicy ==
        "near-json-ft-transfer-args-bounded-v1(max-wire=786,ws=32,order=any,keys=raw,unknown=reject)" &&
      transfer.outputSchema == some .unit && transfer.outputPolicy == "near-void-empty-v1" &&
      transfer.paramCount == 15 && transfer.tupleArity.isNone do
    throwError "ft_transfer lost payable bounded-input or empty-output target policy"
  let some transferCall := program.entries.find? (·.ixName == "ft_transfer_call")
    | throwError "missing target ft_transfer_call"
  unless transferCall.kind == .increment &&
      transferCall.entryPolicy == "near.entry.v1:payable" &&
      transferCall.inputSchema == some Codec.ftTransferCallArgsSchema &&
      transferCall.inputPolicy ==
        "near-json-ft-transfer-call-args-bounded-v1(max-wire=1179,ws=32,order=any,keys=raw,unknown=reject)" &&
      transferCall.outputSchema.isNone && transferCall.outputPolicy.isEmpty &&
      transferCall.paramCount == 24 do
    throwError s!"ft_transfer_call metadata: kind={repr transferCall.kind}, entry={transferCall.entryPolicy}, " ++
      s!"input={repr transferCall.inputSchema}/{transferCall.inputPolicy}, " ++
      s!"output={repr transferCall.outputSchema}/{transferCall.outputPolicy}, params={transferCall.paramCount}"
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
      "(func (export \"ft_metadata\")",
      "(func (export \"storage_balance_of\")",
      "(func (export \"storage_balance_bounds\")",
      "(func (export \"storage_deposit\")",
      "(func (export \"storage_withdraw\")",
      "(func (export \"ft_transfer\")",
      "(func (export \"ft_transfer_call\")",
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
  unless !supplyBody.contains "(call $pf_input" &&
      (supplyBody.splitOn "(call $pf_value_return").length == 2 &&
      !supplyBody.contains "(call $pf_storage_write" &&
      !supplyBody.contains "(call $pf_storage_remove" &&
      !supplyBody.contains "(call $pf_log_utf8" &&
      !supplyBody.contains "(call $pf_promise" do
    throwError "ft_total_supply must ignore request bytes and value_return once without effects"
  let metadataBody ← match wat.splitOn "(func (export \"ft_metadata\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "ft_metadata must occur exactly once"
  unless !metadataBody.contains "(call $pf_input" &&
      (metadataBody.splitOn "(call $pf_value_return").length == 2 &&
      metadataBody.contains "(call $pf_arena_alloc (i64.const 2929)" &&
      !metadataBody.contains "(call $pf_storage_write" &&
      !metadataBody.contains "(call $pf_storage_remove" &&
      !metadataBody.contains "(call $pf_log_utf8" &&
      !metadataBody.contains "(call $pf_promise" do
    throwError "ft_metadata must ignore request bytes and return once without ledger effects"
  let storageBalanceBody ← match wat.splitOn "(func (export \"storage_balance_of\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "storage_balance_of must occur exactly once"
  unless (storageBalanceBody.splitOn "(call $pf_input").length == 2 &&
      storageBalanceBody.contains "(call $pf_storage_read" &&
      !storageBalanceBody.contains "(call $pf_storage_write" &&
      !storageBalanceBody.contains "(call $pf_storage_remove" &&
      !storageBalanceBody.contains "(call $pf_log_utf8" &&
      !storageBalanceBody.contains "(call $pf_promise" do
    throwError "storage_balance_of must parse/read/return without mutation or effects"
  let storageBoundsBody ← match wat.splitOn "(func (export \"storage_balance_bounds\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "storage_balance_bounds must occur exactly once"
  unless storageBoundsBody.contains "(call $pf_value_return" &&
      !storageBoundsBody.contains "(call $pf_storage_write" &&
      !storageBoundsBody.contains "(call $pf_storage_remove" &&
      !storageBoundsBody.contains "(call $pf_log_utf8" &&
      !storageBoundsBody.contains "(call $pf_promise" do
    throwError "storage_balance_bounds must return without ledger mutation/effects"
  let storageDepositBody ← match wat.splitOn "(func (export \"storage_deposit\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "storage_deposit must occur exactly once"
  unless storageDepositBody.contains "(call $pf_json_storage_deposit_args" &&
      storageDepositBody.contains "(call $pf_attached_deposit" &&
      storageDepositBody.contains "(call $pf_storage_read" &&
      storageDepositBody.contains "(call $pf_storage_write" &&
      storageDepositBody.contains "(call $pf_storage_usage" &&
      storageDepositBody.contains "(call $pf_promise_batch_action_transfer" &&
      storageDepositBody.contains "(call $pf_value_return" &&
      !storageDepositBody.contains "(call $pf_storage_remove" &&
      !storageDepositBody.contains "(call $pf_log_utf8" do
    throwError "storage_deposit lost parse/read/write/measure/refund/result composition"
  let storageWithdrawBody ← match wat.splitOn "(func (export \"storage_withdraw\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "storage_withdraw must occur exactly once"
  unless storageWithdrawBody.contains "(i64.const 279)" &&
      storageWithdrawBody.contains "(call $pf_json_storage_withdraw_args" &&
      storageWithdrawBody.contains "(call $pf_attached_deposit" &&
      storageWithdrawBody.contains "(call $pf_storage_read" &&
      storageWithdrawBody.contains "(call $pf_value_return" &&
      !storageWithdrawBody.contains "(call $pf_storage_write" &&
      !storageWithdrawBody.contains "(call $pf_storage_remove" &&
      !storageWithdrawBody.contains "(call $pf_log_utf8" &&
      !storageWithdrawBody.contains "(call $pf_promise" do
    throwError "storage_withdraw lost guard/read/result no-effect composition"
  let storageUnregisterBody ← match wat.splitOn "(func (export \"storage_unregister\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "storage_unregister must occur exactly once"
  unless storageUnregisterBody.contains "(i64.const 47)" &&
      storageUnregisterBody.contains "(call $pf_json_storage_unregister_args" &&
      storageUnregisterBody.contains "(call $pf_attached_deposit" &&
      storageUnregisterBody.contains "(call $pf_storage_read" &&
      storageUnregisterBody.contains "(call $pf_storage_remove" &&
      storageUnregisterBody.contains "(call $pf_promise_batch_action_transfer" &&
      storageUnregisterBody.contains "(call $pf_log_utf8" &&
      storageUnregisterBody.contains "(call $pf_value_return" &&
      !storageUnregisterBody.contains "(call $pf_value_return (i64.const 8)" do
    throwError "storage_unregister lost parse/guard/read/precheck/remove/refund/log/Boolean composition"
  let beforeRemove := storageUnregisterBody.splitOn "(call $pf_storage_remove" |>.headD ""
  let afterRemove := (storageUnregisterBody.splitOn "(call $pf_storage_remove").getD 1 ""
  unless beforeRemove.contains "(call $pf_storage_read" &&
      !beforeRemove.contains "(call $pf_promise_batch_action_transfer" &&
      afterRemove.contains "(call $pf_promise_batch_action_transfer" do
    throwError "storage_unregister must precheck balance/supply/cost/refund before removal"
  let legacyNoArgsBody ← match wat.splitOn "(func (export \"balanceSelfHas\")" with
    | [_before, tail] =>
        match tail.splitOn "\n  )\n" with
        | body :: _ => pure body
        | [] => throwError "balanceSelfHas body terminator is missing"
    | _ => throwError "balanceSelfHas must occur exactly once"
  unless legacyNoArgsBody.contains "(call $pf_input" &&
      legacyNoArgsBody.contains "(call $pf_register_len" do
    throwError "unannotated zero-parameter methods no longer enforce exact-empty input"
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
  let transferCallBody ← match wat.splitOn "(func (export \"ft_transfer_call\")" with
    | [_before, tail] => pure ((tail.splitOn "\n  (func (export").headD "")
    | _ => throwError "ft_transfer_call must occur exactly once"
  let transferCallDeposit := transferCallBody.splitOn "(call $pf_attached_deposit"
  let transferCallReads := transferCallBody.splitOn
    "(global.set $pf_storage_result_status (call $pf_storage_read"
  let transferCallWrites := transferCallBody.splitOn
    "(global.set $pf_storage_result_status (call $pf_storage_write"
  let transferCallLogs := transferCallBody.splitOn "(call $pf_log_utf8"
  unless (transferCallBody.splitOn "(call $pf_input").length == 2 &&
      transferCallDeposit.length == 2 &&
      !transferCallDeposit[0]!.contains "(global.set $pf_storage_result_status" &&
      transferCallReads.length == 3 && transferCallWrites.length == 3 &&
      !transferCallWrites[1]!.contains "(call $pf_log_utf8" &&
      transferCallWrites[2]!.contains "(call $pf_log_utf8" &&
      transferCallLogs.length == 3 &&
      (transferCallBody.splitOn "(call $pf_promise_batch_create").length == 3 &&
      (transferCallBody.splitOn "(call $pf_promise_batch_then").length == 3 &&
      (transferCallBody.splitOn
        "(call $pf_promise_batch_action_function_call_weight").length == 5 &&
      (transferCallBody.splitOn "(call $pf_promise_return").length == 3 &&
      !transferCallBody.contains "(call $pf_value_return" &&
      !transferCallBody.contains "(call $pf_storage_remove" &&
      !transferCallBody.contains
        "(call $pf_storage_write (i64.const 8) (i64.const 1024)" &&
      !transferCallBody.contains
        "(call $pf_storage_write (i64.const 8) (i64.const 1032)" do
    throwError "ft_transfer_call lost guard/read/write/event/DAG/returned-Promise ordering"
  for branch in #[transferCallLogs[1]!, transferCallLogs[2]!] do
    let afterCreate ← match branch.splitOn "(call $pf_promise_batch_create" with
      | [_before, after] => pure after
      | _ => throwError "ft_transfer_call event branch must create one child Promise"
    let weighted := afterCreate.splitOn "(call $pf_promise_batch_action_function_call_weight"
    unless weighted.length == 3 &&
        weighted[1]!.contains "(i64.const 14) (i64.const 8192)" &&
        weighted[1]!.contains "(i64.const 0) (i64.const 1))" &&
        weighted[1]!.contains "(call $pf_promise_batch_then" &&
        weighted[2]!.contains "(i64.const 19) (i64.const 8206)" &&
        weighted[2]!.contains "(i64.const 5000000000000) (i64.const 0))" do
      throwError s!"ft_transfer_call weighted order changed: count={weighted.length}, " ++
        s!"childMethod={weighted[1]?.map (·.contains "(i64.const 14) (i64.const 8192)")}, " ++
        s!"childWeight={weighted[1]?.map (·.contains "(i64.const 0) (i64.const 1))")}, " ++
        s!"then={weighted[1]?.map (·.contains "(call $pf_promise_batch_then")}, " ++
        s!"callbackMethod={weighted[2]?.map (·.contains "(i64.const 19) (i64.const 8206)")}, " ++
        s!"callbackGas={weighted[2]?.map (·.contains "(i64.const 5000000000000) (i64.const 0))")}"
    let afterCallback := weighted[2]!
    let persisted := afterCallback.splitOn
      "(drop (call $pf_storage_write (i64.const 6) (i64.const 1040)"
    unless persisted.length == 2 && persisted[1]!.contains "(call $pf_promise_return" do
      throwError "ft_transfer_call must persist state before returning its callback Promise"
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
  some "e1e290ddec221fa5"

end Tests.NearFungibleLedgerSpec
