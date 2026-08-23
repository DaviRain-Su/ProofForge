import ProofForge.Svm.Assemble
import ProofForge.Golden

def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  for program in ProofForge.Golden.programs do
    let lowered ← match ProofForge.Svm.IR.fromProgram program with
    | .ok lowered => pure lowered
    | .error _ =>
      IO.println s!"skip svm assemble {program.name} (evm leaf)"
      continue
    let r ← ProofForge.Svm.Assemble.assembleIRProgram out lowered
    IO.println s!"wrote {r.asmPath} {r.soPath} {r.idlPath} ({r.soBytes.size} bytes)"
  return 0
