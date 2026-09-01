import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit

namespace ProofForge.Wasm.Near.Assemble

structure Result where
  watPath : System.FilePath
  wasmPath : System.FilePath
  watSource : String

def requiredWat2WasmVersion : String := "1.0.41"

/-- `wat2wasm 1.0.41` prints `1.0.41` on stdout. -/
def parseWat2WasmVersion (stdout : String) : Option String :=
  let tok := stdout.trimAscii.toString
  if tok.isEmpty then none else some tok

private def requireWat2Wasm : IO System.FilePath := do
  let homeBin :=
    match (← IO.getEnv "HOME") with
    | some home => some (System.FilePath.mk home / ".local" / "bin" / "wat2wasm")
    | none => none
  let mut candidates : Array System.FilePath := #[
    "/usr/local/bin/wat2wasm",
    "wat2wasm"
  ]
  if let some p := homeBin then
    candidates := #[p] ++ candidates
  let mut mismatch : Option String := none
  for c in candidates do
    let proc? ←
      try
        some <$> IO.Process.output { cmd := c.toString, args := #["--version"] }
      catch _ =>
        pure none
    match proc? with
    | some proc =>
      if proc.exitCode == 0 then
        match parseWat2WasmVersion proc.stdout with
        | some v =>
            if v == requiredWat2WasmVersion || v.startsWith s!"{requiredWat2WasmVersion}" then
              return c
            else if mismatch.isNone then
              mismatch := some s!"assemble/tool: wat2wasm {v} != {requiredWat2WasmVersion}"
        | none => pure ()
    | none => pure ()
  match mismatch with
  | some reason => throw <| IO.userError reason
  | none => throw <| IO.userError s!"assemble/tool: wat2wasm {requiredWat2WasmVersion} not found"

/-- Render WAT and assemble with locked `wat2wasm`. No rustc / near-sandbox / testnet. -/
def assembleProgram (outDir : System.FilePath) (program : IR.Program) : IO Result := do
  let source ← match Emit.emit program with
    | .error reason => throw <| IO.userError reason
    | .ok src => pure src
  IO.FS.createDirAll outDir
  let watPath := outDir / s!"{program.name}.wat"
  let wasmPath := outDir / s!"{program.name}.wasm"
  IO.FS.writeFile watPath source
  if ← wasmPath.pathExists then
    IO.FS.removeFile wasmPath
  let wat2wasm ← requireWat2Wasm
  let proc ← IO.Process.output {
    cmd := wat2wasm.toString
    args := #[watPath.toString, "-o", wasmPath.toString]
  }
  unless proc.exitCode == 0 do
    if ← wasmPath.pathExists then
      IO.FS.removeFile wasmPath
    throw <| IO.userError s!"assemble/tool: wat2wasm failed\n{proc.stderr}\n{proc.stdout}"
  unless (← wasmPath.pathExists) do
    throw <| IO.userError s!"assemble/tool: wat2wasm did not produce {wasmPath}"
  let wasm ← IO.FS.readBinFile wasmPath
  unless wasm.size ≥ 4 && wasm[0]! == 0x00 && wasm[1]! == 0x61 &&
      wasm[2]! == 0x73 && wasm[3]! == 0x6d do
    IO.FS.removeFile wasmPath
    throw <| IO.userError s!"assemble/tool: wat2wasm produced invalid wasm at {wasmPath}"
  return { watPath, wasmPath, watSource := source }

end ProofForge.Wasm.Near.Assemble
