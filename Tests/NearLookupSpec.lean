import Examples.NearLookup
import Lean
import ProofForge

/-! Direct Identity LookupMap/LookupSet layout, extraction, and WAT invariants. -/

namespace Tests.NearLookupSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard DirectLookupMap64.wellFormed 0x3150414d
#guard DirectLookupSet64.wellFormed 0x31544553
#guard !DirectLookupMap64.wellFormed 0x100000000
#guard DirectAccountNearTokenMap.wellFormed 0x314c4142

private def maximumAccount : ProofForge.Wasm.Near.Runtime.AccountId :=
  { length := 64, w0 := 0x0706050403020100, w1 := 0x0f0e0d0c0b0a0908,
    w2 := 0x1716151413121110, w3 := 0x1f1e1d1c1b1a1918,
    w4 := 0x2726252423222120, w5 := 0x2f2e2d2c2b2a2928,
    w6 := 0x3736353433323130, w7 := 0x3f3e3d3c3b3a3938 }

private def maximumAccountKey : ProofForge.Core.Value.BoundedBytes 72 :=
  (0x314c4142 : DirectAccountNearTokenMap).elementKey maximumAccount

#guard maximumAccountKey.length == 72
#guard maximumAccountKey.values[0] == 0x42
#guard maximumAccountKey.values[3] == 0x31
#guard maximumAccountKey.values[4] == 64
#guard maximumAccountKey.values[8] == 0
#guard maximumAccountKey.values[71] == 63

private def shortAccount : ProofForge.Wasm.Near.Runtime.AccountId :=
  { length := 2, w0 := 0x6161, w1 := 0, w2 := 0, w3 := 0,
    w4 := 0, w5 := 0, w6 := 0, w7 := 0 }
private def tooShortAccount := { shortAccount with length := 1 }
private def tooLongAccount := { maximumAccount with length := 65 }
#guard DirectAccountNearTokenMap.accountLengthValid shortAccount
#guard DirectAccountNearTokenMap.accountLengthValid maximumAccount
#guard !DirectAccountNearTokenMap.accountLengthValid tooShortAccount
#guard !DirectAccountNearTokenMap.accountLengthValid tooLongAccount

private def mapKey : ProofForge.Core.Value.BoundedBytes 12 :=
  (0x3150414d : DirectLookupMap64).elementKey 0x0102030405060708

#guard mapKey.length == 12
#guard mapKey.values[0] == 0x4d
#guard mapKey.values[1] == 0x41
#guard mapKey.values[2] == 0x50
#guard mapKey.values[3] == 0x31
#guard mapKey.values[4] == 0x08
#guard mapKey.values[5] == 0x07
#guard mapKey.values[6] == 0x06
#guard mapKey.values[7] == 0x05
#guard mapKey.values[8] == 0x04
#guard mapKey.values[9] == 0x03
#guard mapKey.values[10] == 0x02
#guard mapKey.values[11] == 0x01

private def mapValue : ProofForge.Core.Value.BoundedBytes 8 :=
  (0x3150414d : DirectLookupMap64).elementValue 0x8877665544332211

#guard mapValue.length == 8
#guard mapValue.values[0] == 0x11
#guard mapValue.values[7] == 0x88

private def setValue : ProofForge.Core.Value.BoundedBytes 1 :=
  (0x31544553 : DirectLookupSet64).elementValue

#guard setValue.length == 0

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key value _ _)) =>
          #[s!"write.{result}.{key}.{value}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ext (.near (.storageHasKey result key _)) => #[s!"has.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

elab "#pf_near_lookup_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearLookup with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "mapGet" == #["read.8.12"] &&
      methodSteps "mapHas" == #["has.8.12"] &&
      methodSteps "mapPut" == #["write.8.12.8"] &&
      methodSteps "mapRemove" == #["remove.8.12"] &&
      methodSteps "setHas" == #["has.1.12"] &&
      methodSteps "setInsert" == #["write.1.12.1"] &&
      methodSteps "setRemove" == #["remove.1.12"] &&
      methodSteps "tokenPutSelfMixed" == #["write.16.72.16"] &&
      methodSteps "tokenPutCallerMax" == #["write.16.72.16"] &&
      methodSteps "tokenPutShortFixture" == #["write.16.72.16"] &&
      methodSteps "tokenSeedSelfMalformed8" == #["write.16.72.20"] &&
      methodSteps "tokenSeedSelfMalformed20" == #["write.16.72.20"] &&
      methodSteps "tokenHasShortFixture" == #["has.16.72"] &&
      methodSteps "tokenReadShortW0" == #["read.16.72"] &&
      methodSteps "tokenRemoveShortFixture" == #["remove.16.72"] do
    throwError s!"direct lookup storage effects were lost or reordered: " ++
      s!"get={methodSteps "mapGet"}, has={methodSteps "mapHas"}, " ++
      s!"put={methodSteps "mapPut"}, remove={methodSteps "mapRemove"}, " ++
      s!"setHas={methodSteps "setHas"}, setInsert={methodSteps "setInsert"}, " ++
      s!"setRemove={methodSteps "setRemove"}, self={methodSteps "tokenPutSelfMixed"}, " ++
      s!"caller={methodSteps "tokenPutCallerMax"}, short={methodSteps "tokenPutShortFixture"}, " ++
      s!"malformed8={methodSteps "tokenSeedSelfMalformed8"}, " ++
      s!"malformed20={methodSteps "tokenSeedSelfMalformed20"}, " ++
      s!"shortHas={methodSteps "tokenHasShortFixture"}, " ++
      s!"shortRead={methodSteps "tokenReadShortW0"}, " ++
      s!"shortRemove={methodSteps "tokenRemoveShortFixture"}, " ++
      s!"methods={source.methods.map (·.ixName)}"
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
  let anchors := #[
    "(func (export \"mapGet\")",
    "(func (export \"mapPut\")",
    "(func (export \"mapRemove\")",
    "(func (export \"setInsert\")",
    "(func (export \"setRemove\")",
    "(func (export \"tokenPutSelfMixed\")",
    "(func (export \"tokenPutCallerMax\")",
    "(func (export \"tokenPutShortFixture\")",
    "(func (export \"tokenSeedSelfMalformed8\")",
    "(func (export \"tokenSeedSelfMalformed20\")",
    "(func (export \"tokenReadShortW0\")",
    "(func (export \"tokenRemoveShortFixture\")",
    "(call $pf_arena_alloc (i64.const 72) (i64.const 1))",
    "(i64.const 16)",
    "(call $pf_storage_has_key",
    "(call $pf_storage_read",
    "(call $pf_storage_write",
    "(call $pf_storage_remove",
    "(i64.const 12)",
    "i64.and",
    "i64.shr_u",
    "i64.shl",
    "i64.or"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR direct lookup WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-lookup: digest = {IR.digestHex program}"

#pf_near_lookup_check

end Tests.NearLookupSpec
