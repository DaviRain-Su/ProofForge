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
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"registerCaller\")", "(func (export \"probeCaller\")",
      "(func (export \"unregisterCaller\")", "(func (export \"seedCallerZero\")",
      "(func (export \"forceUnregisterCaller\")",
      "(func (export \"storage_balance_of\")",
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
  logInfo m!"proofforge-near-storage-registration: digest = {IR.digestHex program}"

#pf_near_storage_registration_check

#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨0, 0⟩
#guard ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨1, 0⟩
#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨2, 0⟩
#guard !ProofForge.Wasm.Near.Sdk.Fungible.Registration.attachedIsOne ⟨1, 1⟩

#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageRegistration" ==
  some "d15fa3f4bcdbdfe"

end Tests.NearStorageRegistrationSpec
