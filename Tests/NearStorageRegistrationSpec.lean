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
  let steps := registrationSteps register.ops
  unless steps == #["read", "usage", "write", "usage", "refund", "refund"] do
    throwError s!"registration effect order changed: {steps}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"registerCaller\")", "(func (export \"probeCaller\")",
      "(call $pf_storage_read", "(call $pf_storage_write", "(call $pf_storage_usage)",
      "(call $pf_promise_batch_create", "(call $pf_promise_batch_action_transfer",
      "(call $pf_mul64_lo", "(call $pf_mul64_hi", "i64.ge_u", "i64.sub",
      "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
      "(call $pf_arena_alloc (i64.const 16) (i64.const 8))"] do
    unless wat.contains anchor do
      throwError s!"NEAR storage registration WAT missing {anchor}\n{wat}"
  if wat.contains "storage_byte_cost" then
    throwError "registration fabricated a nonexistent storage_byte_cost host import"
  logInfo m!"proofforge-near-storage-registration: digest = {IR.digestHex program}"

#pf_near_storage_registration_check

#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageRegistration" ==
  some "551039da8ad472c9"

end Tests.NearStorageRegistrationSpec
