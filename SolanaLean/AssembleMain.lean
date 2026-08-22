import SolanaLean.Assemble
import SolanaLean.Golden

def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  for program in SolanaLean.Golden.programs do
    let r ← SolanaLean.Assemble.assembleProgram out program
    IO.println s!"wrote {r.asmPath} and {r.soPath} ({r.soBytes.size} bytes)"
  return 0
