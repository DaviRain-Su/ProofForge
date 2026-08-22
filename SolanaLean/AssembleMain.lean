import SolanaLean.Assemble
import SolanaLean.IR

def main (args : List String) : IO UInt32 := do
  let out :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/sbpf"
  let counter ← SolanaLean.Assemble.assembleProgram out SolanaLean.IR.extractedCounter
  IO.println s!"wrote {counter.asmPath} and {counter.soPath} ({counter.soBytes.size} bytes)"
  let pair ← SolanaLean.Assemble.assembleProgram out SolanaLean.IR.extractedPair
  IO.println s!"wrote {pair.asmPath} and {pair.soPath} ({pair.soBytes.size} bytes)"
  return 0
