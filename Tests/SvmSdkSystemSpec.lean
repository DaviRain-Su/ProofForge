import ProofForge.Svm.Sdk.System
import Examples.Svm.SysAlloc
import Examples.Svm.Nonce
import Examples.Svm.SysSeed
import Examples.Svm.SysXfer

open Lean Elab Command

namespace Tests.SvmSdkSystemSpec

open ProofForge.Svm.Sdk

#guard System.assign == 0
#guard System.allocate 16 == 0
#guard System.allocate 0 == 0
#guard System.advanceNonce == 0
#guard System.AsciiSeed.wellFormed "ledger"
#guard !System.AsciiSeed.wellFormed ""
#guard !System.AsciiSeed.wellFormed "λ"
#guard System.AsciiSeed.allocate "ledger" 16 == 0
#guard System.AsciiSeed.createAccount "ledger" 7 16 == 0
#guard System.AsciiSeed.createRentExempt "ledger" 16 == 0
#guard System.AsciiSeed.assign "ledger" == 0
#guard System.AsciiSeed.transfer "ledger" 7 == 0

namespace AlternateSeed

@[pf_entry]
def allocateLedger (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.allocate "ledger" 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

@[pf_entry]
def createLedger (_s : Examples.Svm.SysSeed.State) (lamports : UInt64) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.createAccount "ledger" lamports 16
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[pf_entry]
def createRentExemptLedger (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.createRentExempt "ledger" 16
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def assignLedger (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.assign "ledger"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def transferLedger (_s : Examples.Svm.SysSeed.State) (lamports : UInt64) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.transfer "ledger" lamports
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[pf_entry]
def allocateEmpty (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.allocate "" 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

@[pf_entry]
def allocateLong (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.allocate "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

@[pf_entry]
def allocateNonAscii (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := System.AsciiSeed.allocate "λ" 16
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

@[pf_entry]
def allocateBadLength (_s : Examples.Svm.SysSeed.State) :
    Except Examples.Svm.SysSeed.Error (Examples.Svm.SysSeed.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Svm.Runtime.invoke 2
      #[{ acc := 1, signer := false, writable := true },
        { acc := 0, signer := true, writable := false }]
      #[.u32le 9, .accKey 0, .u64le 5, .ascii "ledger", .u64le 16, .programId]
    .ok ({ dummy := 0 }, 16)
  else
    .error .overflow

end AlternateSeed

private def expectCanonical (module : Name) (expected : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let actual := ProofForge.Svm.IR.digestHex program
  unless actual == expected do
    throwError s!"{module}: SDK facade changed canonical IR: {actual}"

elab "#pf_guard_svm_system_facades" : command => do
  expectCanonical `Examples.Svm.SysAlloc "dbb2269b9ac57a3"
  expectCanonical `Examples.Svm.Nonce "5746ebbdd382bd56"
  expectCanonical `Examples.Svm.SysSeed "490cec59af518f0c"
  expectCanonical `Examples.Svm.SysXfer "906efee37227cb35"

#pf_guard_svm_system_facades

private def extractAlternate (env : Environment) (mutation : Name) :
    Except String ProofForge.Svm.IR.Program := do
  let source ← ProofForge.Extract.extractProgramIR env ``Examples.Svm.SysSeed.init mutation
    ``Examples.Svm.SysSeed.get
  ProofForge.Svm.IR.fromExtracted source

private def hasInstructionData
    (program : ProofForge.Svm.IR.Program)
    (expected : Array (ProofForge.Svm.Ops.CpiWord ProofForge.Svm.Ops.Val)) : Bool :=
  program.methods.any fun method => method.ops.any fun
    | .invoke _ _ data #[] none => data == expected
    | _ => false

elab "#pf_guard_svm_alternate_system_seed" : command => do
  let env ← getEnv
  let extract (mutation : Name) : CommandElabM ProofForge.Svm.IR.Program := do
    match extractAlternate env mutation with
    | .ok program => pure program
    | .error reason => throwError reason
  let allocate ← extract ``AlternateSeed.allocateLedger
  let create ← extract ``AlternateSeed.createLedger
  let createRentExempt ← extract ``AlternateSeed.createRentExemptLedger
  let assign ← extract ``AlternateSeed.assignLedger
  let transfer ← extract ``AlternateSeed.transferLedger
  unless hasInstructionData allocate
      #[.u32le (.lit 9), .accKey 0, .u64le (.lit 6), .ascii "ledger", .u64le (.lit 16),
        .programId] &&
      hasInstructionData create
        #[.u32le (.lit 3), .accKey 0, .u64le (.lit 6), .ascii "ledger", .u64le (.arg 0),
          .u64le (.lit 16), .programId] &&
      hasInstructionData createRentExempt
        #[.u32le (.lit 3), .accKey 0, .u64le (.lit 6), .ascii "ledger",
          .u64le (.ext (.component (.sysvar (.rentExemption 16))) #[]),
          .u64le (.lit 16), .programId] &&
      hasInstructionData assign
        #[.u32le (.lit 10), .accKey 0, .u64le (.lit 6), .ascii "ledger", .programId] &&
      hasInstructionData transfer
        #[.u32le (.lit 11), .u64le (.arg 0), .u64le (.lit 6), .ascii "ledger", .programId] do
    throwError "generic seeded System facade did not preserve the alternate literal and its length"

#pf_guard_svm_alternate_system_seed

elab "#pf_guard_svm_system_seed_policy" : command => do
  let env ← getEnv
  for mutation in #[``AlternateSeed.allocateEmpty, ``AlternateSeed.allocateLong,
      ``AlternateSeed.allocateNonAscii, ``AlternateSeed.allocateBadLength] do
    match extractAlternate env mutation with
    | .error reason =>
        unless reason.contains "System seed must be 1-32 ASCII bytes with matching length" ||
            reason.contains "malformed SVM Ops" do
          throwError s!"{mutation}: unexpected seed-policy error: {reason}"
    | .ok _ => throwError s!"{mutation}: malformed System seed was accepted"

#pf_guard_svm_system_seed_policy

end Tests.SvmSdkSystemSpec
