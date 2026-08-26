import ProofForge.Svm.Emit
import ProofForge.Svm.Idl

namespace ProofForge.Svm.Assemble

open ProofForge.Svm

structure Result where
  asmPath : System.FilePath
  soPath : System.FilePath
  idlPath : System.FilePath
  soBytes : ByteArray

/-- Agave 4.0 Loader-v3 stores ELF bytes after 45 bytes of `ProgramData` metadata in an account
whose protocol maximum is 10 MiB. Keep this pure boundary explicit so tests can pin both edges. -/
def loaderV3ProgramDataMetadataBytes : Nat := 45

def loaderV3MaxProgramDataBytes : Nat := 10 * 1024 * 1024

def loaderV3MaxElfBytes : Nat :=
  loaderV3MaxProgramDataBytes - loaderV3ProgramDataMetadataBytes

def loaderV3SizeEligible (elfBytes : Nat) : Bool :=
  loaderV3ProgramDataMetadataBytes + elfBytes ≤ loaderV3MaxProgramDataBytes

/-- ELF 64-bit LSB shared object, eBPF：前 4 字节 `\x7fELF`，EI_CLASS=2。 -/
def looksLikeElf (bytes : ByteArray) : Bool :=
  bytes.size ≥ 5 &&
    bytes[0]! == 0x7f &&
    bytes[1]! == 0x45 &&
    bytes[2]! == 0x4c &&
    bytes[3]! == 0x46 &&
    bytes[4]! == 2

private def runSbpf (projectRoot deployDir : System.FilePath) : IO Unit := do
  let proc ← IO.Process.output {
    cmd := "sbpf"
    args := #["build", "-d", deployDir.toString]
    cwd := projectRoot
  }
  unless proc.exitCode == 0 do
    throw <| IO.userError s!"assemble/tool: sbpf failed\n{proc.stderr}"

partial def findFileNamed (dir : System.FilePath) (name : String) : IO (Option System.FilePath) := do
  if !(← dir.pathExists) then
    return none
  let entries ← dir.readDir
  for e in entries do
    let p := e.path
    if e.fileName == name then
      return some p
    if (← p.isDir) then
      if let some hit ← findFileNamed p name then
        return some hit
  return none

private def assembleOutput (outDir : System.FilePath) (name asm idl : String) : IO Result := do
  let soName := s!"{name}.so"
  -- `sbpf build` compiles every source under its project root. Keep each program isolated so a
  -- stale or failed source from one build cannot poison later, otherwise unrelated programs fail.
  let project := outDir / "sbpf-project" / name
  let srcDir := project / "src" / name
  let deployDir := project / "deploy"
  IO.FS.createDirAll srcDir
  IO.FS.createDirAll deployDir
  let asmPath := srcDir / s!"{name}.s"
  IO.FS.writeFile asmPath asm
  runSbpf project deployDir
  let some soPath ← findFileNamed project soName
    | throw <| IO.userError s!"assemble/tool: sbpf did not produce {soName}"
  let soBytes ← IO.FS.readBinFile soPath
  unless looksLikeElf soBytes do
    throw <| IO.userError "assemble/tool: output is not ELF"
  unless soBytes.size > 0 do
    throw <| IO.userError "assemble/tool: empty ELF"
  unless loaderV3SizeEligible soBytes.size do
    throw <| IO.userError
      s!"assemble/size: ELF is {soBytes.size} bytes; Loader-v3 limit is {loaderV3MaxElfBytes}"
  let stagedAsm := outDir / s!"{name}.s"
  let stagedSo := outDir / soName
  let stagedIdl := outDir / s!"{name}.idl.json"
  IO.FS.writeFile stagedAsm asm
  IO.FS.writeBinFile stagedSo soBytes
  IO.FS.writeFile stagedIdl idl
  return { asmPath := stagedAsm, soPath := stagedSo, idlPath := stagedIdl, soBytes }

/-- Assemble a fully lowered SVM target program with the local `sbpf` toolchain. -/
def assembleIRProgram (outDir : System.FilePath) (program : IR.Program) : IO Result := do
  let asm ← match Emit.emitAsm program with
    | .error reason => throw <| IO.userError reason
    | .ok text => pure text
  assembleOutput outDir program.name asm (Idl.emitProgramIdl program)

end ProofForge.Svm.Assemble
