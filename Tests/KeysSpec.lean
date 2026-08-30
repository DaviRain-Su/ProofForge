import Examples.Keys
import Lean

namespace Tests.KeysSpec

open Examples.Keys
open ProofForge.Svm.Runtime
open Lean Elab Command

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard key00 (init 0) == accKeyWord 0 0
#guard key03 (init 0) == accKeyWord 0 3
#guard owner00 (init 0) == accOwnerWord 0 0
#guard key10 (init 0) == accKeyWord 1 0
#guard owner13 (init 0) == accOwnerWord 1 3
#guard accKeyWord 0 0 == 0
#guard accOwnerWord 1 3 == 0

#guard !ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedKeys
#guard ProofForge.Svm.ABI.usesWalk ProofForge.Golden.extractedKeys
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedKeys == 2

/-- The modern whole-Pubkey boundary is derived from the generic static record schema. It must
not add a Pubkey-specific Runtime/IR/component/emitter operation. -/
elab "#pf_guard_keys_pubkey_boundary" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Keys with
    | .ok source => pure source
    | .error reason => throwError reason
  let pubkeySchema := ProofForge.Core.Codec.Schema.record "ProofForge.Svm.Sdk.Pubkey" #[
    ("word0", .scalar .uint64), ("word1", .scalar .uint64),
    ("word2", .scalar .uint64), ("word3", .scalar .uint64)]
  let some peer := source.methods.find? (·.ixName == "peerKey")
    | throwError "missing peerKey"
  unless ProofForge.Attr.isBoundary env ``ProofForge.Svm.Sdk.Pubkey &&
      peer.paramCount == 0 && peer.retSchema == pubkeySchema && peer.retCount == 4 do
    throwError "whole-Pubkey source schema was not preserved"
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some peer := program.methods.find? (·.ixName == "peerKey")
    | throwError "missing projected peerKey"
  match peer.entry with
  | .raw output =>
      unless output.tag == 26 && output.accountCount == 2 && output.paramCount == 0 &&
          output.inferredReturnWidths == #[8, 8, 8, 8] && output.dataLen == 1 &&
          output.returnDataLen == 32 do
        throwError s!"wrong whole-Pubkey plan: {repr output}"
  | .generated => throwError "whole-Pubkey entry lost its raw adapter"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "call peerKey" && asm.contains "jne r1, 1, err_raw_peerKey" &&
      asm.contains "load walked acc1 +8" && asm.contains "load walked acc1 +32" &&
      !asm.contains "sol_invoke" && !asm.contains "alloc" do
    throwError "whole-Pubkey boundary gained unexpected geometry or low-level vocabulary"

#pf_guard_keys_pubkey_boundary

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedKeys with
  | .error _ => false
  | .ok asm =>
      asm.contains "load acc0 key word 0" &&
        asm.contains "load acc0 key word 3" &&
        asm.contains "load acc0 owner word 0" &&
        asm.contains "load acc0 owner word 3" &&
        asm.contains "load walked acc1 +8" &&
        asm.contains "load walked acc1 +32" &&
        asm.contains "load walked acc1 +40" &&
        asm.contains "load walked acc1 +64" &&
        asm.contains "jlt r1, 2" &&
        asm.contains "call key00" &&
        asm.contains "call key10" &&
        !asm.contains "call sol_invoke_signed_c" &&
        !asm.contains "ja key00"

end Tests.KeysSpec
