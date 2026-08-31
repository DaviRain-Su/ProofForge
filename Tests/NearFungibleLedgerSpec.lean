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
      methodSteps "burnSelfOne" ==
        #["read.16.72", "remove.16.72", "write.16.72.16"] &&
      methodSteps "transferCallerToSelfOne" ==
        #["read.16.72", "read.16.72", "remove.16.72", "write.16.72.16",
          "write.16.72.16", "write.16.72.16"] &&
      methodSteps "seedSelfMalformed8" == #["write.16.72.20"] &&
      methodSteps "seedSelfMalformed20" == #["write.16.72.20"] do
    throwError s!"fungible ledger effects lost prerequisite reads or write-last branches: " ++
      s!"mint={methodSteps "mintSelfOne"}, burn={methodSteps "burnSelfOne"}, " ++
      s!"transfer={methodSteps "transferCallerToSelfOne"}, " ++
      s!"malformed8={methodSteps "seedSelfMalformed8"}, " ++
      s!"malformed20={methodSteps "seedSelfMalformed20"}"
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
  for anchor in #[
      "(func (export \"mintSelfOne\")", "(func (export \"mintSelfTwo64\")",
      "(func (export \"mintSelfMax\")", "(func (export \"burnSelfOne\")",
      "(func (export \"transferCallerToSelfOne\")",
      "(func (export \"transferCallerToSelfZero\")",
      "(func (export \"seedSelfMalformed8\")",
      "(func (export \"fixtureSetSupplyMax\")",
      "(call $pf_storage_read", "(call $pf_storage_write", "(call $pf_storage_remove",
      "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
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
  logInfo m!"proofforge-near-fungible-ledger: digest = {IR.digestHex program}"

#pf_near_fungible_ledger_check

#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleLedger" ==
  some "b91759b7d8a8fac7"

end Tests.NearFungibleLedgerSpec
