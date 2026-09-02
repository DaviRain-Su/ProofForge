import ProofForge.Svm.Sdk.AssociatedToken
import ProofForge.Svm.Sdk.Memo
import Examples.Svm.Ata
import Examples.Svm.Memo

open Lean Elab Command

namespace Tests.SvmSdkProgramSpec

open ProofForge.Svm.Sdk

#guard AssociatedToken.createIdempotent == 0
#guard AssociatedToken.create == 0
#guard AssociatedToken.recoverNested == 0
#guard AssociatedToken.fixedCreateAccounts.wellFormed
#guard AssociatedToken.fixedRecoverNestedAccounts.wellFormed
#guard !(AssociatedToken.CreateAccounts.at 63 0 1 2 3 4 5).wellFormed
#guard !(AssociatedToken.RecoverNestedAccounts.at 7 0 1 2 3 4 5 63).wellFormed
#guard Memo.writeOk == 0
#guard Memo.Ascii.maxBytes == 512
#guard Memo.Ascii.wellFormed "proof-forge"
#guard Memo.Ascii.wellFormed (String.ofList (List.replicate 512 'a'))
#guard !Memo.Ascii.wellFormed (String.ofList (List.replicate 513 'a'))
#guard !Memo.Ascii.wellFormed "λ"

namespace AlternateMemo

@[pf_entry]
def writeProofForge (_s : Examples.Svm.Memo.State) :
    Except Examples.Svm.Memo.Error (Examples.Svm.Memo.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := Memo.Ascii.write "proof-forge"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def writeNonAscii (_s : Examples.Svm.Memo.State) :
    Except Examples.Svm.Memo.Error (Examples.Svm.Memo.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := Memo.Ascii.write "λ"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

end AlternateMemo

namespace GeneralAta

@[pf_inline] def roleCreateAccounts : AssociatedToken.CreateAccounts :=
  { associatedTokenProgram := .at 8
    payer := .at 1
    associatedAccount := .at 2
    wallet := .at 3
    mint := .at 4
    systemProgram := .at 5
    tokenProgram := .at 6 }

@[pf_inline] def roleRecoverAccounts : AssociatedToken.RecoverNestedAccounts :=
  { associatedTokenProgram := .at 10
    nestedAssociatedAccount := .at 1
    nestedMint := .at 2
    destinationAssociatedAccount := .at 3
    ownerAssociatedAccount := .at 4
    ownerMint := .at 5
    wallet := .at 6
    tokenProgram := .at 8 }

@[pf_entry]
def create (_s : Examples.Svm.Ata.State) :
    Except Examples.Svm.Ata.Error (Examples.Svm.Ata.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := AssociatedToken.create
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def recoverNested (_s : Examples.Svm.Ata.State) :
    Except Examples.Svm.Ata.Error (Examples.Svm.Ata.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := AssociatedToken.recoverNested
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def createWithRoles (_s : Examples.Svm.Ata.State) :
    Except Examples.Svm.Ata.Error (Examples.Svm.Ata.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := AssociatedToken.createIdempotentWith roleCreateAccounts
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def recoverWithRoles (_s : Examples.Svm.Ata.State) :
    Except Examples.Svm.Ata.Error (Examples.Svm.Ata.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := AssociatedToken.recoverNestedWith roleRecoverAccounts
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

end GeneralAta

private def memoInvokeWellFormed (payload : String) : Bool :=
  ProofForge.Svm.Ops.OpExt.wellFormed
    (.invoke 1 #[{ acc := 0, signer := true, writable := false }] #[.ascii payload] #[] none)

private def genericAsciiInvokeWellFormed (payload : String) : Bool :=
  ProofForge.Svm.Ops.OpExt.wellFormed (.invoke 2 #[] #[.ascii payload] #[] none)

#guard memoInvokeWellFormed (String.ofList (List.replicate 512 'a'))
#guard !memoInvokeWellFormed (String.ofList (List.replicate 513 'a'))
#guard !memoInvokeWellFormed "λ"
#guard genericAsciiInvokeWellFormed "λ"
#guard genericAsciiInvokeWellFormed (String.ofList (List.replicate 513 'a'))

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

elab "#pf_guard_svm_program_facades" : command => do
  expectCanonical `Examples.Svm.Ata "574dc90c21ca9723"
  expectCanonical `Examples.Svm.Memo "26a3540da902ccb5"

#pf_guard_svm_program_facades

private def extractAlternateMemo (env : Environment) (mutation : Name) :
    Except String ProofForge.Svm.IR.Program := do
  let source ← ProofForge.Extract.extractProgramIR env ``Examples.Svm.Memo.init mutation
    ``Examples.Svm.Memo.get
  ProofForge.Svm.IR.fromExtracted source

elab "#pf_guard_svm_bounded_memo" : command => do
  let env ← getEnv
  let program ←
    match extractAlternateMemo env ``AlternateMemo.writeProofForge with
    | .ok program => pure program
    | .error reason => throwError reason
  unless program.methods.any fun method => method.ops.any fun
      | .invoke 1 metas #[.ascii "proof-forge"] #[] none =>
          metas == #[{ acc := 0, signer := true, writable := false }]
      | _ => false do
    throwError "bounded Memo facade did not preserve the alternate static payload"
  match extractAlternateMemo env ``AlternateMemo.writeNonAscii with
  | .error reason =>
      unless reason.contains "Memo payload must be at most 512 ASCII bytes" ||
          reason.contains "malformed SVM Ops" do
        throwError s!"unexpected Memo policy error: {reason}"
  | .ok _ => throwError "non-ASCII Memo payload was accepted"

#pf_guard_svm_bounded_memo

private def extractAtaMethod (env : Environment) (mutation : Name) :
    Except String ProofForge.Svm.IR.Program := do
  let source ← ProofForge.Extract.extractProgramIR env ``Examples.Svm.Ata.init mutation
    ``Examples.Svm.Ata.get
  ProofForge.Svm.IR.fromExtracted source

elab "#pf_guard_svm_general_ata" : command => do
  let env ← getEnv
  let ordinary ←
    match extractAtaMethod env ``GeneralAta.create with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ordinary.methods.any fun method => method.ops.any fun
      | .invoke 6 metas #[.u8le (.lit 0)] #[] none =>
          metas == #[{ acc := 0, signer := true, writable := true },
            { acc := 1, writable := true }, { acc := 2 }, { acc := 3 }, { acc := 4 },
            { acc := 5 }]
      | _ => false do
    throwError "ordinary ATA Create did not preserve the official account geometry"
  let recover ←
    match extractAtaMethod env ``GeneralAta.recoverNested with
    | .ok program => pure program
    | .error reason => throwError reason
  unless recover.methods.any fun method => method.ops.any fun
      | .invoke 7 metas #[.u8le (.lit 2)] #[] none =>
          metas == #[{ acc := 0, writable := true }, { acc := 1 },
            { acc := 2, writable := true }, { acc := 3 }, { acc := 4 },
            { acc := 5, signer := true, writable := true }, { acc := 6 }]
      | _ => false do
    throwError "ATA RecoverNested did not preserve the official account geometry"
  let roleSelected ←
    match extractAtaMethod env ``GeneralAta.createWithRoles with
    | .ok program => pure program
    | .error reason => throwError reason
  unless roleSelected.methods.any fun method => method.ops.any fun
      | .invoke 8 metas #[.u8le (.lit 1)] #[] none =>
          metas == #[{ acc := 1, signer := true, writable := true },
            { acc := 2, writable := true }, { acc := 3 }, { acc := 4 }, { acc := 5 },
            { acc := 6 }]
      | _ => false do
    throwError "ATA role plan did not preserve caller-selected accounts"
  let recoverRoleSelected ←
    match extractAtaMethod env ``GeneralAta.recoverWithRoles with
    | .ok program => pure program
    | .error reason => throwError reason
  unless recoverRoleSelected.methods.any fun method => method.ops.any fun
      | .invoke 10 metas #[.u8le (.lit 2)] #[] none =>
          metas == #[{ acc := 1, writable := true }, { acc := 2 },
            { acc := 3, writable := true }, { acc := 4 }, { acc := 5 },
            { acc := 6, signer := true, writable := true }, { acc := 8 }]
      | _ => false do
    throwError "ATA RecoverNested role plan did not preserve caller-selected accounts"

#pf_guard_svm_general_ata

end Tests.SvmSdkProgramSpec
