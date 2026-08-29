import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Emit

namespace ProofForge.Wasm.Xrpl.Assemble

structure Result where
  rsPath : System.FilePath
  rsSource : String

/-- Zero-tool v0 assembly: render the Bedrock-dialect Rust source and write it out. No
rustc / cargo / bedrock / AlphaNet step is claimed or performed here. -/
def assembleProgram (outDir : System.FilePath) (program : IR.Program) : IO Result := do
  let source ← match Emit.emit program with
    | .error reason => throw <| IO.userError reason
    | .ok src => pure src
  IO.FS.createDirAll outDir
  let rsPath := outDir / s!"{program.name}.rs"
  IO.FS.writeFile rsPath source
  return { rsPath, rsSource := source }

end ProofForge.Wasm.Xrpl.Assemble