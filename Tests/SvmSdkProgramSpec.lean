import ProofForge.Svm.Sdk.AssociatedToken
import ProofForge.Svm.Sdk.Memo
import Examples.Ata
import Examples.Memo

open Lean Elab Command

namespace Tests.SvmSdkProgramSpec

open ProofForge.Svm.Sdk

#guard AssociatedToken.createIdempotent == 0
#guard Memo.writeOk == 0
#guard Memo.Ascii.maxBytes == 512
#guard Memo.Ascii.wellFormed "proof-forge"
#guard Memo.Ascii.wellFormed (String.ofList (List.replicate 512 'a'))
#guard !Memo.Ascii.wellFormed (String.ofList (List.replicate 513 'a'))
#guard !Memo.Ascii.wellFormed "λ"

namespace AlternateMemo

@[pf_entry]
def writeProofForge (_s : Examples.Memo.State) :
    Except Examples.Memo.Error (Examples.Memo.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := Memo.Ascii.write "proof-forge"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def writeNonAscii (_s : Examples.Memo.State) :
    Except Examples.Memo.Error (Examples.Memo.State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := Memo.Ascii.write "λ"
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

end AlternateMemo

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
  expectCanonical `Examples.Ata "574dc90c21ca9723"
  expectCanonical `Examples.Memo "26a3540da902ccb5"

#pf_guard_svm_program_facades

private def extractAlternateMemo (env : Environment) (mutation : Name) :
    Except String ProofForge.Svm.IR.Program := do
  let source ← ProofForge.Extract.extractProgramIR env ``Examples.Memo.init mutation
    ``Examples.Memo.get
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

end Tests.SvmSdkProgramSpec
