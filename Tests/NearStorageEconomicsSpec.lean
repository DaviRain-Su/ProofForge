import Examples.NearStorageEconomics
import Lean
import ProofForge

/-! Dynamic nearcore storage-usage host leaf and storage-delta fixture invariants. -/

namespace Tests.NearStorageEconomicsSpec

open Lean Elab Command
open ProofForge.Wasm.Near

private partial def usageCount : ProofForge.Extract.IR.Val → Nat
  | .ext (.near .storageUsage) operands => 1 + operands.foldl (init := 0) (· + usageCount ·)
  | .field base _ | .bitNot base => usageCount base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs => usageCount lhs + usageCount rhs
  | .indexGet base _ index _ _ => usageCount base + usageCount index
  | .select _ lhs rhs thn els =>
      usageCount lhs + usageCount rhs + usageCount thn + usageCount els
  | .ext _ operands => operands.foldl (init := 0) (· + usageCount ·)
  | _ => 0

private partial def economicsSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .letLocal _ value | .setLocal _ value => Array.replicate (usageCount value) "usage"
      | .returnU64 value | .returnState value | .okState value | .storeField _ value =>
          Array.replicate (usageCount value) "usage"
      | .ext (.near (.storageWrite ..)) => #["write"]
      | .ext (.near (.storageRemove ..)) => #["remove"]
      | .ite _ lhs rhs thn els => Array.replicate (usageCount lhs + usageCount rhs) "usage" ++
          economicsSteps thn ++ economicsSteps els
      | .forBody _ body => economicsSteps body
      | _ => #[]

elab "#pf_near_storage_economics_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearStorageEconomics with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (economicsSteps ·.ops) |>.getD #[]
  unless methodSteps "usage" == #["usage"] &&
      methodSteps "insertShort4" == #["usage", "write", "usage"] &&
      methodSteps "replaceShort4" == #["usage", "write", "usage"] &&
      methodSteps "removeShort" == #["usage", "remove", "usage"] &&
      methodSteps "removeMissing" == #["usage", "remove", "usage"] do
    throwError s!"storage usage/effect ordering changed: usage={methodSteps "usage"}, " ++
      s!"insert={methodSteps "insertShort4"}, replace={methodSteps "replaceShort4"}, " ++
      s!"remove={methodSteps "removeShort"}, missing={methodSteps "removeMissing"}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(import \"env\" \"storage_usage\" (func $pf_storage_usage (result i64)))",
      "(func (export \"usage\")", "(func (export \"insertShort4\")",
      "(func (export \"replaceShort4\")", "(func (export \"growShort8\")",
      "(func (export \"removeShort\")", "(func (export \"removeMissing\")",
      "(func (export \"insertLong4\")", "(call $pf_storage_usage)",
      "(call $pf_storage_write", "(call $pf_storage_remove",
      "(i64.sub (local.get $pf_v1) (local.get $pf_v0))"] do
    unless wat.contains anchor do
      throwError s!"NEAR storage economics WAT missing {anchor}\n{wat}"
  unless (wat.splitOn "(call $pf_storage_usage)").length == 16 do
    throwError "NEAR storage economics must sample once in its view and twice around each effect"
  if wat.contains "storage_byte_cost" then
    throwError "NEAR storage economics fabricated a nonexistent storage_byte_cost host import"
  logInfo m!"proofforge-near-storage-economics: digest = {IR.digestHex program}"

#pf_near_storage_economics_check

#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorageEconomics" ==
  some "9c98eca433f99470"

end Tests.NearStorageEconomicsSpec
