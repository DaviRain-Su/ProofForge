import ProofForge.Svm.Assemble
import ProofForge.Golden
import ProofForge.Ops

def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  for program in ProofForge.Golden.programs do
    if program.methods.any (fun m => ProofForge.Ops.hasEvmEffect m.ops) then
      IO.println s!"skip svm assemble {program.name} (evm leaf)"
      continue
    let r ← ProofForge.Svm.Assemble.assembleProgram out program
    IO.println s!"wrote {r.asmPath} {r.soPath} {r.idlPath} ({r.soBytes.size} bytes)"
  return 0
