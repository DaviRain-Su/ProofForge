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
  let flag ← SolanaLean.Assemble.assembleProgram out SolanaLean.IR.extractedFlag
  IO.println s!"wrote {flag.asmPath} and {flag.soPath} ({flag.soBytes.size} bytes)"
  let maybe ← SolanaLean.Assemble.assembleProgram out SolanaLean.IR.extractedMaybe
  IO.println s!"wrote {maybe.asmPath} and {maybe.soPath} ({maybe.soBytes.size} bytes)"
  let window ← SolanaLean.Assemble.assembleProgram out SolanaLean.IR.extractedWindow
  IO.println s!"wrote {window.asmPath} and {window.soPath} ({window.soBytes.size} bytes)"
  return 0
