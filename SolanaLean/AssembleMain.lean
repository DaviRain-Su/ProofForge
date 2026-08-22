import SolanaLean.Assemble
import SolanaLean.IR

def main (args : List String) : IO UInt32 := do
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  let result ← SolanaLean.Assemble.assembleCounter out SolanaLean.IR.extractedCounter
  IO.println s!"wrote {result.asmPath} and {result.soPath} ({result.soBytes.size} bytes)"
  return 0
