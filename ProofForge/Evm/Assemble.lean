import ProofForge.Evm.IR
import ProofForge.Evm.Emit

namespace ProofForge.Evm.Assemble

open ProofForge.Evm

/-- EVM bytecode assembler selection. Default remains solc (Feature A). -/
inductive Backend where
  | solc
  | yulc
  deriving BEq, Repr, Inhabited

def parseBackend (s : String) : Option Backend :=
  match s.trimAscii.toString with
  | "solc" => some .solc
  | "yulc" => some .yulc
  | _ => none

def backendFromEnv : IO Backend := do
  match ← IO.getEnv "PROOFFORGE_EVM_BACKEND" with
  | some "yulc" => pure .yulc
  | some "solc" => pure .solc
  | _ => pure .solc

structure Result where
  yulPath : System.FilePath
  abiPath : System.FilePath
  binPath : System.FilePath
  binHex : String
  backend : Backend := .solc

def requiredSolcVersion : String := "0.8.34"

/-- Pin opcode semantics as well as compiler syntax. In particular opcode `0x44` is
`PREVRANDAO`, never the pre-Paris `DIFFICULTY` interpretation. -/
def requiredEvmVersion : String := "cancun"

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
        match parseSolcVersion proc.stdout with
        | some v =>
            if v == requiredSolcVersion then
              return c
            else if mismatch.isNone then
              mismatch := some s!"assemble/tool: solc {v} != {requiredSolcVersion}"
        | none => pure ()
    | none => pure ()
  match mismatch with
  | some reason => throw <| IO.userError reason
  | none => throw <| IO.userError s!"assemble/tool: solc {requiredSolcVersion} not found"

private def yulcCandidates (repoRoot : System.FilePath) : Array System.FilePath := #[
  repoRoot / "powdr-probe/.lake/packages/yul_evm_compiler/.lake/build/bin/yulc",
  repoRoot / "powdr-probe/.lake/build/bin/yulc",
  System.FilePath.mk "yulc"
]

private def requireYulc (repoRoot : System.FilePath) : IO System.FilePath := do
  for c in yulcCandidates repoRoot do
    if c.toString != "yulc" then
      if ← c.pathExists then
        return c
    else
      let proc ← IO.Process.output { cmd := "bash", args := #["-lc", "command -v yulc 2>/dev/null"] }
      if proc.exitCode == 0 && !proc.stdout.trimAscii.isEmpty then
        return System.FilePath.mk "yulc"
  throw <| IO.userError
    "assemble/tool: yulc not found; run scripts/build_yulc.sh or set PROOFFORGE_YULC to the binary path"

private def resolveYulc (repoRoot : System.FilePath) : IO System.FilePath := do
  match ← IO.getEnv "PROOFFORGE_YULC" with
  | some path =>
    let c := System.FilePath.mk path
    return c
  | none => requireYulc repoRoot

private def assembleBytecode (backend : Backend) (repoRoot : System.FilePath)
    (outDir : System.FilePath) (programName : String) : IO String := do
  match backend with
  | .solc =>
    let solc ← requireSolc
    let proc ← IO.Process.output {
      cmd := solc.toString
      args := #["--strict-assembly", "--optimize", "--evm-version", requiredEvmVersion,
        "--bin", s!"{programName}.yul"]
      cwd := outDir
    }
    unless proc.exitCode == 0 do
      throw <| IO.userError s!"assemble/tool: solc failed\n{proc.stderr}"
    match parseBytecode proc.stdout with
    | .ok h => pure h
    | .error reason => throw <| IO.userError reason
  | .yulc =>
    let yulc ← resolveYulc repoRoot
    let yulFile := outDir / s!"{programName}.yul"
    let proc ← IO.Process.output {
      cmd := yulc.toString
      args := #["--backend=classic", yulFile.toString]
    }
    if proc.exitCode == 2 then
      throw <| IO.userError
        s!"assemble/tool: yulc rejected {programName}.yul (outside verified fragment; see scripts/check_yul_fragment.py)\n{proc.stderr}"
    unless proc.exitCode == 0 do
      throw <| IO.userError s!"assemble/tool: yulc failed\n{proc.stderr}"
    let hex := proc.stdout.trimAscii.toString
    if hex.isEmpty then
      throw <| IO.userError "assemble/tool: yulc returned no bytecode"
    else if !looksLikeHex hex then
      throw <| IO.userError "assemble/tool: yulc bytecode is not hex"
    else
      pure hex

def assembleProgramWithBackend (outDir : System.FilePath) (program : IR.Program)
    (backend : Backend) : IO Result := do
  let repoRoot ← IO.currentDir
  let (yul, abi) ← match Emit.emit program with
    | .error reason => throw <| IO.userError reason
    | .ok pair => pure pair
  IO.FS.createDirAll outDir
  let yulPath := outDir / s!"{program.name}.yul"
  let abiPath := outDir / s!"{program.name}.abi.json"
  let binPath := outDir / s!"{program.name}.bin"
  IO.FS.writeFile yulPath yul
  IO.FS.writeFile abiPath abi
  let hex ← assembleBytecode backend repoRoot outDir program.name
  IO.FS.writeFile binPath (hex ++ "\n")
  return { yulPath, abiPath, binPath, binHex := hex, backend }

def assembleProgram (outDir : System.FilePath) (program : IR.Program) : IO Result := do
  let backend ← backendFromEnv
  assembleProgramWithBackend outDir program backend

end ProofForge.Evm.Assemble
