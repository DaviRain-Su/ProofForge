import Examples.NearStorageRegistration
import Lean
import ProofForge

/-! Closed caller-only measured storage-registration extraction and WAT invariants. -/

namespace Tests.NearStorageRegistrationSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private partial def registrationSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead ..)) => #["read"]
      | .ext (.near (.storageWrite ..)) => #["write"]
      | .ext (.near (.storageRemove ..)) => #["remove"]
      | .ext (.near (.storageUnregisteredLog ..)) => #["missing-log"]
      | .ext (.near (.promiseTransferAccountDetached ..)) => #["refund"]
      | .letLocal _ (.ext (.near .storageUsage) _) => #["usage"]
      | .ite _ _ _ thn els => registrationSteps thn ++ registrationSteps els
      | .forBody _ body => registrationSteps body
      | _ => #[]

elab "#pf_near_storage_registration_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearStorageRegistration with
    | .ok program => pure program
    | .error reason => throwError reason
  let register ← match source.methods.find? (·.ixName == "registerCaller") with
    | some method => pure method
    | none => throwError "missing registerCaller"
  let unregister ← match source.methods.find? (·.ixName == "unregisterCaller") with
    | some method => pure method
    | none => throwError "missing unregisterCaller"
  let forceUnregister ← match source.methods.find? (·.ixName == "forceUnregisterCaller") with
    | some method => pure method
    | none => throwError "missing forceUnregisterCaller"
  let balanceOf ← match source.methods.find? (·.ixName == "storage_balance_of") with
    | some method => pure method
    | none => throwError "missing storage_balance_of"
  let bounds ← match source.methods.find? (·.ixName == "storage_balance_bounds") with
    | some method => pure method
    | none => throwError "missing storage_balance_bounds"
  let deposit ← match source.methods.find? (·.ixName == "storage_deposit") with
    | some method => pure method
    | none => throwError "missing storage_deposit"
  let withdraw ← match source.methods.find? (·.ixName == "storage_withdraw") with
    | some method => pure method
    | none => throwError "missing storage_withdraw"
  let publicUnregister ← match source.methods.find? (·.ixName == "storage_unregister") with
    | some method => pure method
    | none => throwError "missing storage_unregister"
  let steps := registrationSteps register.ops
  unless steps == #["read", "usage", "write", "usage", "refund", "refund"] do
    throwError s!"registration effect order changed: {steps}"
  let unregisterSteps := registrationSteps unregister.ops
  unless unregisterSteps == #["read", "usage", "remove", "usage", "refund"] do
    throwError s!"unregister effect order changed: {unregisterSteps}"
  let forceSteps := registrationSteps forceUnregister.ops
  unless forceSteps == #["read", "usage", "remove", "usage", "refund"] do
    throwError s!"force unregister effect order changed: {forceSteps}"
  unless registrationSteps balanceOf.ops == #["read"] &&
      balanceOf.paramSchemas == #[Codec.accountIdSchema] &&
      balanceOf.retSchema == Codec.storageBalanceResultSchema && balanceOf.retCount == 5 do
    throwError "storage_balance_of lost its one-read AccountId/StorageBalance source contract"
  unless registrationSteps bounds.ops == #[] && bounds.paramSchemas.isEmpty &&
      bounds.retSchema == Codec.storageBalanceBoundsResultSchema && bounds.retCount == 5 do
    throwError "storage_balance_bounds lost its no-effect/no-arg exact bounds source contract"
  unless registrationSteps deposit.ops == #["read", "usage", "write", "usage", "refund", "refund"] &&
      deposit.paramSchemas == #[Codec.storageDepositArgsSchema] &&
      deposit.retSchema == Codec.storageBalanceResultSchema && deposit.retCount == 5 do
    throwError "storage_deposit lost its parser/map/refund/StorageBalance source contract"
  unless registrationSteps withdraw.ops == #["read"] &&
      withdraw.paramSchemas == #[Codec.storageWithdrawArgsSchema] &&
      withdraw.retSchema == Codec.storageBalanceResultSchema && withdraw.retCount == 5 do
    throwError "storage_withdraw lost its parser/one-read/StorageBalance source contract"
  unless registrationSteps publicUnregister.ops ==
      #["read", "missing-log", "usage", "remove", "usage", "refund"] &&
      publicUnregister.paramSchemas == #[Codec.storageUnregisterArgsSchema] &&
      publicUnregister.retSchema == Codec.jsonBooleanResultSchema &&
      publicUnregister.retCount == 1 do
    throwError "storage_unregister lost its parser/map/refund/Boolean source contract"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let targetBalanceOf ← match program.entries.find? (·.ixName == "storage_balance_of") with
    | some method => pure method
    | none => throwError "missing target storage_balance_of"
  unless targetBalanceOf.inputSchema == some Codec.accountIdSchema &&
      targetBalanceOf.inputPolicy ==
        "near-json-account-id-object-bounded-v1(max-wire=433,ws=32,keys=canonical,unknown=reject)" &&
      targetBalanceOf.outputSchema == some Codec.storageBalanceResultSchema &&
      targetBalanceOf.outputPolicy == "near-json-storage-balance-option-v1" &&
      targetBalanceOf.tupleArity == some 5 do
    throwError "storage_balance_of did not combine its exact input/output target policies"
  let targetBounds ← match program.entries.find? (·.ixName == "storage_balance_bounds") with
    | some method => pure method
    | none => throwError "missing target storage_balance_bounds"
  unless targetBounds.inputSchema == some .unit &&
      targetBounds.inputPolicy == "near-no-args-ignore-input-v1" &&
      targetBounds.outputSchema == some Codec.storageBalanceBoundsResultSchema &&
      targetBounds.outputPolicy == "near-json-storage-balance-bounds-v1" &&
      targetBounds.paramCount == 0 && targetBounds.tupleArity == some 5 do
    throwError "storage_balance_bounds lost its no-input exact bounds output policy"
  let targetDeposit ← match program.entries.find? (·.ixName == "storage_deposit") with
    | some method => pure method
    | none => throwError "missing target storage_deposit"
  unless targetDeposit.inputSchema == some Codec.storageDepositArgsSchema &&
      targetDeposit.inputPolicy ==
        "near-json-storage-deposit-args-bounded-v1(max-wire=459,ws=32,order=any,keys=raw,unknown=reject)" &&
      targetDeposit.outputSchema == some Codec.storageBalanceResultSchema &&
      targetDeposit.outputPolicy == "near-json-storage-balance-option-v1" &&
      targetDeposit.entryPolicy == "near.entry.v1:payable" &&
      targetDeposit.tupleArity == some 5 do
    throwError "storage_deposit lost its exact mutating input/output/payable target policies"
  let targetWithdraw ← match program.entries.find? (·.ixName == "storage_withdraw") with
    | some method => pure method
    | none => throwError "missing target storage_withdraw"
  unless targetWithdraw.inputSchema == some Codec.storageWithdrawArgsSchema &&
      targetWithdraw.inputPolicy ==
        "near-json-storage-withdraw-args-bounded-v1(max-wire=279,ws=32,digits=1..39,keys=raw,unknown=reject)" &&
      targetWithdraw.outputSchema == some Codec.storageBalanceResultSchema &&
      targetWithdraw.outputPolicy == "near-json-storage-balance-option-v1" &&
      targetWithdraw.entryPolicy == "near.entry.v1:payable" &&
      targetWithdraw.tupleArity == some 5 do
    throwError "storage_withdraw lost its exact mutating input/output/payable target policies"
  let targetPublicUnregister ← match program.entries.find? (·.ixName == "storage_unregister") with
    | some method => pure method
    | none => throwError "missing target storage_unregister"
  unless targetPublicUnregister.inputSchema == some Codec.storageUnregisterArgsSchema &&
      targetPublicUnregister.inputPolicy ==
        "near-json-storage-unregister-args-bounded-v1(max-wire=47,ws=32,keys=raw,unknown=reject)" &&
      targetPublicUnregister.outputSchema == some Codec.jsonBooleanResultSchema &&
      targetPublicUnregister.outputPolicy == "near-json-boolean-v1" &&
      targetPublicUnregister.entryPolicy == "near.entry.v1:payable" &&
      targetPublicUnregister.tupleArity == some 1 do
    throwError "storage_unregister lost its exact mutating input/output/payable target policies"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"registerCaller\")", "(func (export \"probeCaller\")",
      "(func (export \"unregisterCaller\")", "(func (export \"seedCallerZero\")",
      "(func (export \"forceUnregisterCaller\")",
      "(func (export \"storage_balance_of\")",
      "(func (export \"storage_balance_bounds\")",
      "(func (export \"storage_deposit\")",
      "(func (export \"storage_withdraw\")",
      "(func (export \"storage_unregister\")",
      "(func (export \"seedCallerOne\")", "(func (export \"fixtureSetCostMax\")",
      "(func (export \"fixtureSeedCallerMixedSupply\")",
      "(func (export \"fixtureSeedCallerMaxSupply\")",
      "(func (export \"totalSupplyW0\")", "(func (export \"totalSupplyW1\")",
      "(func (export \"fixtureSetCostAddOverflow\")", "(call $pf_storage_read",
      "(call $pf_storage_write", "(call $pf_storage_remove", "(call $pf_storage_usage)",
      "(call $pf_promise_batch_create", "(call $pf_promise_batch_action_transfer",
      "(call $pf_mul64_lo", "(call $pf_mul64_hi", "i64.ge_u", "i64.lt_u",
      "i64.add", "i64.sub",
      "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
      "(call $pf_arena_alloc (i64.const 16) (i64.const 8))",
      "(call $pf_arena_alloc (i64.const 105) (i64.const 1))",
      "(call $pf_arena_alloc (i64.const 97) (i64.const 1))",
      "(func $pf_json_account_id", "(func $pf_u128_decimal"] do
    unless wat.contains anchor do
      throwError s!"NEAR storage registration WAT missing {anchor}\n{wat}"
  if wat.contains "storage_byte_cost" then
    throwError "registration fabricated a nonexistent storage_byte_cost host import"
  let balanceParts := wat.splitOn "(func (export \"storage_balance_of\")"
  unless balanceParts.length == 2 do
    throwError "missing unique storage_balance_of export body"
  let balanceBody := (balanceParts[1]!).splitOn "(func (export \"" |>.head!
  unless balanceBody.contains "(call $pf_storage_read" &&
      !balanceBody.contains "(call $pf_storage_write" &&
      !balanceBody.contains "(call $pf_storage_remove" &&
      !balanceBody.contains "(call $pf_log_utf8" &&
      !balanceBody.contains "(call $pf_promise_" do
    throwError "storage_balance_of must read state/map and have no write/log/Promise effects"
  let boundsParts := wat.splitOn "(func (export \"storage_balance_bounds\")"
  unless boundsParts.length == 2 do
    throwError "missing unique storage_balance_bounds export body"
  let boundsBody := (boundsParts[1]!).splitOn "(func (export \"" |>.head!
  unless !boundsBody.contains "(call $pf_input" &&
      (boundsBody.splitOn "(call $pf_value_return").length == 5 &&
      !boundsBody.contains "(call $pf_storage_write" &&
      !boundsBody.contains "(call $pf_storage_remove" &&
      !boundsBody.contains "(call $pf_log_utf8" &&
      !boundsBody.contains "(call $pf_promise_" do
    throwError "storage_balance_bounds must ignore request bytes and return one branch without effects"
  let depositParts := wat.splitOn "(func (export \"storage_deposit\")"
  unless depositParts.length == 2 do
    throwError "missing unique storage_deposit export body"
  let depositBody := (depositParts[1]!).splitOn "(func (export \"" |>.head!
  unless depositBody.contains "(i64.const 459)" &&
      depositBody.contains "(call $pf_json_storage_deposit_args" &&
      depositBody.contains "(call $pf_storage_read" &&
      depositBody.contains "(call $pf_storage_write" &&
      depositBody.contains "(call $pf_promise_batch_action_transfer" &&
      depositBody.contains "(call $pf_u128_decimal" &&
      depositBody.contains "(call $pf_value_return" &&
      !depositBody.contains "(call $pf_storage_remove" &&
      !depositBody.contains "(call $pf_log_utf8" do
    throwError "storage_deposit lost bounded parse/read-write/refund/exact JSON terminal structure"
  let beforeFirstReturn := depositBody.splitOn "(call $pf_value_return" |>.head!
  for stateStore in #[
      "(call $pf_storage_write (i64.const 9) (i64.const 1050)",
      "(call $pf_storage_write (i64.const 10) (i64.const 1059)",
      "(call $pf_storage_write (i64.const 10) (i64.const 1069)",
      "(call $pf_storage_write (i64.const 8) (i64.const 1105)"] do
    unless beforeFirstReturn.contains stateStore do
      throwError s!"storage_deposit state persistence was not before its JSON terminal: {stateStore}"
  let withdrawParts := wat.splitOn "(func (export \"storage_withdraw\")"
  unless withdrawParts.length == 2 do
    throwError "missing unique storage_withdraw export body"
  let withdrawBody := (withdrawParts[1]!).splitOn "(func (export \"" |>.head!
  unless withdrawBody.contains "(i64.const 279)" &&
      withdrawBody.contains "(call $pf_json_storage_withdraw_args" &&
      withdrawBody.contains "(call $pf_attached_deposit" &&
      withdrawBody.contains "(call $pf_storage_read" &&
      withdrawBody.contains "(call $pf_mul64_lo" &&
      withdrawBody.contains "(call $pf_mul64_hi" &&
      withdrawBody.contains "(call $pf_u128_decimal" &&
      withdrawBody.contains "(call $pf_value_return" &&
      !withdrawBody.contains "(call $pf_storage_remove" &&
      !withdrawBody.contains "(call $pf_log_utf8" &&
      !withdrawBody.contains "(call $pf_promise_" do
    throwError "storage_withdraw lost bounded guard/read/cost/exact JSON no-effect structure"
  let beforeWithdrawRead := withdrawBody.splitOn "(call $pf_storage_read" |>.head!
  unless beforeWithdrawRead.contains "(call $pf_attached_deposit" &&
      !beforeWithdrawRead.contains "(call $pf_storage_write" do
    throwError "storage_withdraw must guard attached yocto before its one map read"
  let unregisterParts := wat.splitOn "(func (export \"storage_unregister\")"
  unless unregisterParts.length == 2 do
    throwError "missing unique storage_unregister export body"
  let unregisterBody := (unregisterParts[1]!).splitOn "(func (export \"" |>.head!
  unless unregisterBody.contains "(i64.const 47)" &&
      unregisterBody.contains "(call $pf_json_storage_unregister_args" &&
      unregisterBody.contains "(call $pf_attached_deposit" &&
      unregisterBody.contains "(call $pf_storage_read" &&
      unregisterBody.contains "(call $pf_storage_remove" &&
      unregisterBody.contains "(call $pf_storage_usage" &&
      unregisterBody.contains "(call $pf_promise_batch_action_transfer" &&
      unregisterBody.contains "(call $pf_value_return (local.get $pf_output_length)" &&
      unregisterBody.contains "(call $pf_arena_alloc (i64.const 94) (i64.const 1))" &&
      unregisterBody.contains "(call $pf_log_utf8" do
    throwError "storage_unregister lost bounded parse/guard/read-remove/refund/Boolean structure"
  let beforeRemove := unregisterBody.splitOn "(call $pf_storage_remove" |>.head!
  unless beforeRemove.contains "(call $pf_storage_read" &&
      !beforeRemove.contains "(call $pf_promise_batch_action_transfer" do
    throwError "storage_unregister must validate its balance/supply before removal/refund"
  let beforeFirstUnregisterReturn := unregisterBody.splitOn "(call $pf_value_return" |>.head!
  unless beforeFirstUnregisterReturn.contains "(call $pf_storage_write" do
    throwError "storage_unregister state persistence was not before its Boolean terminal"
  logInfo m!"proofforge-near-storage-registration: digest = {IR.digestHex program}"

#pf_near_storage_registration_check

#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨0, 0⟩
#guard ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨1, 0⟩
#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨2, 0⟩
#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨1, 1⟩
#guard ProofForge.Wasm.Near.Sdk.Fungible.Registration.minimumAccountEntryBytes == 66
#guard ProofForge.Wasm.Near.Sdk.Fungible.Registration.maximumAccountEntryBytes == 128

#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageRegistration" ==
  some "c8ee999bea20bf6d"

end Tests.NearStorageRegistrationSpec
