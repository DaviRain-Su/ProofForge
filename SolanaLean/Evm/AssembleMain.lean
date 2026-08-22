import SolanaLean.Evm.Assemble
import SolanaLean.Evm.Golden

def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/evm"
  for program in SolanaLean.Evm.Golden.programs do
    let r ← SolanaLean.Evm.Assemble.assembleProgram out program
    IO.println s!"wrote {r.yulPath} {r.abiPath} {r.binPath} ({r.binHex.length / 2} bytes)"
  return 0
