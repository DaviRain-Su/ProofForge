import ProofForge.Evm.IR
import ProofForge.Evm.Emit

namespace ProofForge.Evm.Assemble

open ProofForge.Evm

structure Result where
  yulPath : System.FilePath
  abiPath : System.FilePath
  binPath : System.FilePath
  binHex : String

def requiredSolcVersion : String := "0.8.34"

/-- `solc, the solidity compiler…\nVersion: 0.8.34+commit…` -/
def parseSolcVersion (stdout : String) : Option String :=
  match stdout.splitOn "Version: " with
  | _ :: rest :: _ =>
      let tok := (rest.takeWhile (fun c => c != '+' && c != '\n')).trimAscii.toString
      if tok.isEmpty then none else some tok
  | _ => none

def looksLikeHex (s : String) : Bool :=
  s.length ≥ 2 && s.length % 2 == 0 &&
    s.toList.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def parseBytecode (stdout : String) : Except String String :=
  match stdout.splitOn "Binary representation:\n" with
  | _ :: rest :: _ =>
      let hex := rest.trimAscii.toString
      if hex.isEmpty then
        .error "assemble/tool: solc returned no bytecode"
      else if !looksLikeHex hex then
        .error "assemble/tool: solc bytecode is not hex"
      else
        .ok hex
  | _ => .error "assemble/tool: solc stdout missing Binary representation"

private def requireSolc : IO System.FilePath := do
  let candidates : Array System.FilePath := #[
    "/opt/homebrew/bin/solc",
    "/usr/local/bin/solc",
    "solc"
  ]
  for c in candidates do
    try
      let proc ← IO.Process.output { cmd := c.toString, args := #["--version"] }
      if proc.exitCode == 0 then
        match parseSolcVersion proc.stdout with
        | some v =>
            if v == requiredSolcVersion then
              return c
            else
              throw <| IO.userError
                s!"assemble/tool: solc {v} != {requiredSolcVersion}"
        | none => pure ()
    catch _ =>
      pure ()
  throw <| IO.userError s!"assemble/tool: solc {requiredSolcVersion} not found"

def assembleProgram (outDir : System.FilePath) (program : IR.Program) : IO Result := do
  let (yul, abi) ← match Emit.emit program with
    | .error reason => throw <| IO.userError reason
    | .ok pair => pure pair
  IO.FS.createDirAll outDir
  let yulPath := outDir / s!"{program.name}.yul"
  let abiPath := outDir / s!"{program.name}.abi.json"
  let binPath := outDir / s!"{program.name}.bin"
  IO.FS.writeFile yulPath yul
  IO.FS.writeFile abiPath abi
  let solc ← requireSolc
  let proc ← IO.Process.output {
    cmd := solc.toString
    args := #["--strict-assembly", "--optimize", "--bin", s!"{program.name}.yul"]
    cwd := outDir
  }
  unless proc.exitCode == 0 do
    throw <| IO.userError s!"assemble/tool: solc failed\n{proc.stderr}"
  let hex ← match parseBytecode proc.stdout with
    | .ok h => pure h
    | .error reason => throw <| IO.userError reason
  IO.FS.writeFile binPath (hex ++ "\n")
  return { yulPath, abiPath, binPath, binHex := hex }

end ProofForge.Evm.Assemble
