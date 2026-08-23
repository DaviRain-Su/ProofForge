import ProofForge.Svm.Emit
import ProofForge.Extract.LegacyIR
import ProofForge.Svm.Idl

namespace ProofForge.Svm.Assemble

open ProofForge.Svm

structure Result where
  asmPath : System.FilePath
  soPath : System.FilePath
  idlPath : System.FilePath
  soBytes : ByteArray

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

/-- 把 `program` 汇编写成 `src/Name/Name.s`，调用本机 `sbpf 0.2.2`。 -/
def assembleProgram (outDir : System.FilePath) (program : Extract.Legacy.Program) : IO Result := do
  let asm ← match Emit.emitCounterAsm program with
    | .error reason => throw <| IO.userError reason
    | .ok text => pure text
  let name := program.name
  let soName := s!"{name}.so"
  let project := outDir / "sbpf-project"
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
  let stagedAsm := outDir / s!"{name}.s"
  let stagedSo := outDir / soName
  let stagedIdl := outDir / s!"{name}.idl.json"
  IO.FS.writeFile stagedAsm asm
  IO.FS.writeBinFile stagedSo soBytes
  IO.FS.writeFile stagedIdl (Idl.emitIdl program)
  return { asmPath := stagedAsm, soPath := stagedSo, idlPath := stagedIdl, soBytes }

def assembleCounter (outDir : System.FilePath) (program : Extract.Legacy.Program) :
    IO Result :=
  assembleProgram outDir program

end ProofForge.Svm.Assemble
