import SolanaLean.Assemble
import SolanaLean.Golden
import SolanaLean.Ops

def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  for program in SolanaLean.Golden.programs do
    if program.methods.any (fun m => Ops.hasEvmLeaf m.ops) then
      IO.println s!"skip svm assemble {program.name} (evm leaf)"
      continue
    let r ← SolanaLean.Assemble.assembleProgram out program
    IO.println s!"wrote {r.asmPath} and {r.soPath} ({r.soBytes.size} bytes)"
  return 0
