import Examples.NearTokenStorage
import Lean
import ProofForge

/-! Exact 16-byte little-endian Borsh NearToken storage-value codec invariants. -/

namespace Tests.NearTokenStorageSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

private def encoded := borshNearToken
  ({ w0 := 0x0102030405060708, w1 := 0x1112131415161718 } : ProofForge.Core.Value.UInt128)

#guard encoded.length == 16
#guard encoded.values[0] == 0x08
#guard encoded.values[7] == 0x01
#guard encoded.values[8] == 0x18
#guard encoded.values[15] == 0x11

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key value _ _)) => #[s!"write.{result}.{key}.{value}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ext (.near (.storageHasKey result key _)) => #[s!"has.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

elab "#pf_near_token_storage_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearTokenStorage with
    | .ok program => pure program
    | .error reason => throwError reason
  let methodSteps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless methodSteps "readW0" == #["read.16.4"] &&
      methodSteps "readW1" == #["read.16.4"] &&
      methodSteps "staleAfterMissW0" == #["read.16.4", "read.16.4"] &&
      methodSteps "putMixed" == #["write.16.4.16"] &&
      methodSteps "putMax" == #["write.16.4.16"] &&
      methodSteps "putZero" == #["write.16.4.16"] &&
      methodSteps "putShort" == #["write.16.4.8"] &&
      methodSteps "putOversized" == #["write.16.4.20"] &&
      methodSteps "remove" == #["remove.16.4"] &&
      methodSteps "has" == #["has.16.4"] do
    throwError s!"NearToken storage effects lost/reordered: read={methodSteps "readW0"}, " ++
      s!"stale={methodSteps "staleAfterMissW0"}, mixed={methodSteps "putMixed"}, " ++
      s!"short={methodSteps "putShort"}, oversized={methodSteps "putOversized"}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"readW0\")", "(func (export \"readW1\")",
      "(func (export \"putMixed\")", "(func (export \"putShort\")",
      "(func (export \"putOversized\")", "(func (export \"remove\")",
      "(call $pf_storage_read", "(call $pf_storage_write", "(call $pf_storage_remove",
      "(i64.const 16)", "(i64.const 20)", "i64.shl", "i64.or"] do
    unless wat.contains anchor do
      throwError s!"NEAR token storage WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-token-storage: digest = {IR.digestHex program}"

#pf_near_token_storage_check
#pf_near_build Examples.NearTokenStorage

#guard ProofForge.Wasm.Near.Registry.digestOf "NearTokenStorage" == some "92e4c2bf2a7f74a0"

end Tests.NearTokenStorageSpec
