import Lean
import ProofForge.Extract
import ProofForge.Core.IR
import ProofForge.Svm.Assemble
import ProofForge.Svm.Registry
import ProofForge.Evm.Assemble
import ProofForge.Evm.IR
import ProofForge.Evm.Registry
import ProofForge.Wasm.Xrpl.Assemble
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Registry
import ProofForge.Wasm.Near.Assemble
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Registry

namespace ProofForge.Cli

/-- A target names one concrete chain. `wasm` is a chain family, not a target: it is
rejected with a hint so callers pick a member (e.g. `xrpl` or `near`). -/
inductive Target where
  | svm
  | evm
  | xrpl
  | xrplAlphaNet
  | near
  deriving BEq, Repr, Inhabited

def parseTarget : String → Option Target
  | "svm" | "solana" | "sbpf" => some .svm
  | "evm" => some .evm
  | "xrpl" | "xrpl-bedrock" | "bedrock" => some .xrpl
  | "xrpl-alphanet" | "alphanet" => some .xrplAlphaNet
  | "near" => some .near
  | _ => none

inductive Command where
  | build
  | deploy
  | call
  | init
  deriving BEq, Repr, Inhabited

structure Options where
  command : Command := .build
  target : Target := .svm
  outDir : System.FilePath := "build/out"
  names : Array String := #[]
  evmBackend : Option ProofForge.Evm.Assemble.Backend := none
  /-- Fully-qualified Lean modules (`MyProgram.Counter`). Overrides in-tree fixture mapping when set. -/
  modules : Array String := #[]
  /-- Project directory name for `pf init`. -/
  initName : String := ""
  rpcUrl : String := "https://alphanet.xrpl.org"
  wallet : String := "snoPBrXtMeMyMHUVTgbuqAfg1SUTb"
  contract : String := ""
  functionName : String := ""
  callArgs : Array String := #[]
  /-- Create-time tfSendAmount drops. Empty = no InstanceParameterValues. -/
  sendAmount : String := ""
  help : Bool := false
  version : Bool := false

private def usage : String :=
  "pf — ProofForge compiler\n" ++
    "\n" ++
    "Usage:\n" ++
    "  pf build --target <svm|evm|xrpl|xrpl-alphanet|near> [--out DIR] [--backend solc|yulc] [--module MOD] [Program ...]\n" ++
    "  pf init <name> --target <svm|evm>\n" ++
    "  pf deploy --target <xrpl|xrpl-alphanet> [--out DIR] [--rpc URL] [--wallet SEED] [--send-amount DROPS] Program\n" ++
    "  pf call --target <xrpl|xrpl-alphanet> --contract ACCOUNT [--rpc URL] [--wallet SEED] Function [UINT64 ...]\n" ++
    "  pf --version\n" ++
    "\n" ++
    "svm  writes Name.so / Name.s / Name.idl.json\n" ++
    "evm  writes Name.bin / Name.yul / Name.abi.json (default backend solc; --backend yulc or PROOFFORGE_EVM_BACKEND=yulc)\n" ++
    "xrpl writes Name.wat / Name.wasm (XRPL Bedrock local; locked wat2wasm)\n" ++
    "xrpl-alphanet same IR, XLS-0102 host names for live AlphaNet\n" ++
    "near writes Name.wat / Name.wasm (NEAR raw-u64; locked wat2wasm)\n" ++
    "--module takes a dotted Lean module (repeatable). Bare Program names map to in-tree Examples fixtures.\n" ++
    "User projects should pass --module or list [[program]] entries in pf.toml.\n" ++
    "No program names on build means every registered source module for the selected target.\n"

def parseArgs (args : List String) : Except String Options :=
  let rec go (rest : List String) (o : Options) : Except String Options :=
    match rest with
    | [] => .ok o
    | "-h" :: _ | "--help" :: _ => .ok { o with help := true }
    | "--version" :: _ | "-V" :: _ => .ok { o with version := true }
    | "--target" :: t :: rest =>
      match parseTarget t with
      | some tgt => go rest { o with target := tgt }
      | none =>
          if t == "wasm" then
            .error "wasm is a chain family, not a target; pick a concrete member (e.g. xrpl or near)"
          else .error s!"unknown target {t}"
    | "--out" :: d :: rest => go rest { o with outDir := d }
    | "--module" :: m :: rest => go rest { o with modules := o.modules.push m }
    | "--rpc" :: u :: rest => go rest { o with rpcUrl := u }
    | "--wallet" :: s :: rest => go rest { o with wallet := s }
    | "--contract" :: a :: rest => go rest { o with contract := a }
    | "--send-amount" :: d :: rest => go rest { o with sendAmount := d }
    | "--backend" :: b :: rest =>
      match ProofForge.Evm.Assemble.parseBackend b with
      | some backend => go rest { o with evmBackend := some backend }
      | none => .error s!"unknown evm backend {b} (want solc or yulc)"
    | flag :: rest =>
      if flag.startsWith "--backend=" then
        let b := (flag.replace "--backend=" "").trimAscii.toString
        match ProofForge.Evm.Assemble.parseBackend b with
        | some backend => go rest { o with evmBackend := some backend }
        | none => .error s!"unknown evm backend {b} (want solc or yulc)"
      else if flag.startsWith "-" then .error s!"unknown flag {flag}"
      else if o.command == .init && o.initName.isEmpty then
        go rest { o with initName := flag }
      else if o.command == .call && o.functionName.isEmpty then
        go rest { o with functionName := flag }
      else if o.command == .call then
        go rest { o with callArgs := o.callArgs.push flag }
      else
        go rest { o with names := o.names.push flag }
  let args := args.dropWhile (· == "--")
  let (cmd, rest) :=
    match args with
    | "build" :: rest => (Command.build, rest)
    | "deploy" :: rest => (Command.deploy, rest)
    | "call" :: rest => (Command.call, rest)
    | "init" :: rest => (Command.init, rest)
    | rest => (Command.build, rest)
  let start : Options :=
    match cmd with
    | .deploy | .call => { command := cmd, target := .xrplAlphaNet }
    | .init => { command := cmd, target := .svm }
    | .build => { command := cmd }
  go rest start

private def svmProgramNames : Array String :=
  Svm.Registry.names

private def selectSvmNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok svmProgramNames
  else
    names.mapM fun n =>
      match svmProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown svm program {n}"

/-- Dual-target fixtures stay at `Examples.<Name>`; target-only fixtures live under
`Examples.{Svm,Evm,Xrpl,Near}.<Name>`. Program registry names are the last component. -/
private def sharedFixtureNames : Array String :=
  #["Counter", "Flag", "Lang", "Maybe", "Pair", "Phase", "TokenShape", "Window"]

/-- Ergonomics / handle fixtures not yet moved under `Examples.{Evm,Svm,Near}.`. -/
private def rootTargetFixtureNames (target : Target) : Array String :=
  match target with
  | .evm => #["EvmExceptErgonomics", "EvmTokenErgonomics"]
  | .svm => #["SvmExceptErgonomics"]
  | .near => #["NearPromiseHandle", "NearTokenErgonomics"]
  | _ => #[]

def fixtureModule (target : Target) (name : String) : Lean.Name :=
  if sharedFixtureNames.contains name || (rootTargetFixtureNames target).contains name then
    Lean.Name.str `Examples name
  else
    let family : Lean.Name :=
      match target with
      | .svm => `Examples.Svm
      | .evm => `Examples.Evm
      | .xrpl | .xrplAlphaNet => `Examples.Xrpl
      | .near => `Examples.Near
    Lean.Name.str family name

def svmModuleName (name : String) : Lean.Name :=
  fixtureModule .svm name

structure BuildUnit where
  name : String
  module : Lean.Name
  deriving Repr

private def dottedToName (mod : String) : Lean.Name :=
  (mod.splitOn ".").foldl (fun n p => if p.isEmpty then n else Lean.Name.str n p) .anonymous

private def basenameOfModule (mod : String) : String :=
  match (mod.splitOn ".").getLast? with
  | some n => n
  | none => mod

private def trimStr (s : String) : String :=
  s.trimAscii.toString

private def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

private def dropEndStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

private def unquoteToml (v0 : String) : String :=
  let v := trimStr v0
  if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else if v.startsWith "'" && v.endsWith "'" && v.length ≥ 2 then
    dropEndStr (dropStr v 1) 1
  else v

/-- Value after the first `=` on a TOML assignment line. -/
private def tomlValue (line : String) : Option String :=
  match line.splitOn "=" with
  | _ :: rest =>
    if rest.isEmpty then none
    else some (unquoteToml (String.intercalate "=" rest))
  | _ => none

/-- Minimal `pf.toml` reader: collect `[[program]]` tables with `name` / `module`. -/
private def parsePfTomlPrograms (text : String) : Array BuildUnit := Id.run do
  let mut units : Array BuildUnit := #[]
  let mut inProgram := false
  let mut curName : Option String := none
  let mut curModule : Option String := none
  let flush (units : Array BuildUnit) (curName : Option String) (curModule : Option String) :=
    match curModule with
    | some m =>
      let n := curName.getD (basenameOfModule m)
      units.push { name := n, module := dottedToName m }
    | none => units
  for line0 in text.splitOn "\n" do
    let line := trimStr line0
    if line.isEmpty || line.startsWith "#" then
      pure ()
    else if line == "[[program]]" then
      if inProgram then
        units := flush units curName curModule
      inProgram := true
      curName := none
      curModule := none
    else if inProgram then
      if line.startsWith "name" then
        match tomlValue line with
        | some v => curName := some v
        | none => pure ()
      else if line.startsWith "module" then
        match tomlValue line with
        | some v => curModule := some v
        | none => pure ()
      else if line.startsWith "[" then
        units := flush units curName curModule
        inProgram := false
        curName := none
        curModule := none
  if inProgram then
    units := flush units curName curModule
  units

private def loadPfTomlUnits : IO (Array BuildUnit) := do
  let path : System.FilePath := "pf.toml"
  if !(← path.pathExists) then
    return #[]
  let text ← IO.FS.readFile path
  return parsePfTomlPrograms text

private def resolveUnits (opts : Options)
    (selectNames : Array String → Except String (Array String))
    (tomlUnits : Array BuildUnit) :
    Except String (Array BuildUnit) := do
  if !opts.modules.isEmpty then
    pure <| opts.modules.map fun m =>
      { name := basenameOfModule m, module := dottedToName m }
  else if !opts.names.isEmpty then
    let names ← selectNames opts.names
    pure <| names.map fun n => { name := n, module := fixtureModule opts.target n }
  else if !tomlUnits.isEmpty then
    pure tomlUnits
  else
    let names ← selectNames #[]
    pure <| names.map fun n => { name := n, module := fixtureModule opts.target n }

private def isExamplesModule : Lean.Name → Bool
  | .str .anonymous "Examples" => true
  | .str pref _ => isExamplesModule pref
  | _ => false

/--
CLI builds must re-extract IR from user modules; never assemble legacy Golden smoke fixtures.
The target registry only lists buildable modules and pins canonical digests for Examples fixtures.
-/
private unsafe def extractSvmPrograms (units : Array BuildUnit) :
    IO (Except String (Array Svm.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Svm.IR.fromExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok program =>
        if !isExamplesModule u.module then
          .ok program
        else
          let digest := Svm.IR.digestHex program
          match Svm.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok program
            else .error s!"{u.name}: ir/mismatch: extracted digest {digest} != fixture {expected}"
          | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def evmProgramNames : Array String :=
  Evm.Registry.names

private def selectEvmNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok evmProgramNames
  else
    names.mapM fun n =>
      match evmProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown evm program {n}"

private unsafe def extractEvmPrograms (units : Array BuildUnit) :
    IO (Except String (Array ProofForge.Evm.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Evm.IR.fromExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok program =>
        if !isExamplesModule u.module then
          .ok program
        else
          let digest := Evm.IR.digestHex program
          match Evm.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok program
            else .error s!"{u.name}: ir/mismatch: extracted evm digest {digest} != fixture {expected}"
          | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def xrplProgramNames : Array String :=
  Wasm.Xrpl.Registry.names

private def selectXrplNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok xrplProgramNames
  else
    names.mapM fun n =>
      match xrplProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown xrpl program {n}"

private unsafe def extractXrplPrograms (units : Array BuildUnit) :
    IO (Except String (Array ProofForge.Wasm.Xrpl.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Wasm.Xrpl.IR.fromExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok program =>
        if !isExamplesModule u.module then
          .ok program
        else
          let digest := Wasm.Xrpl.IR.digestHex program
          match Wasm.Xrpl.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok program
            else .error s!"{u.name}: ir/mismatch: extracted xrpl digest {digest} != fixture {expected}"
          | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def findAlphaNetRpc : IO System.FilePath := do
  let cwd ← IO.currentDir
  let here := cwd / "runtime-tests" / "xrpl" / "alphanet-rpc.js"
  if ← here.pathExists then
    return here
  throw <| IO.userError "pf: runtime-tests/xrpl/alphanet-rpc.js not found (run from repo root)"

private def writeTempJson (body : String) : IO System.FilePath := do
  let tmp :=
    match ← IO.getEnv "TMPDIR" with
    | some d => System.FilePath.mk d
    | none => "/tmp"
  let path := tmp / s!"pf-alphanet-{← IO.monoNanosNow}.json"
  IO.FS.writeFile path body
  return path

private def runAlphaNetJs (cmd : String) (cfgPath : System.FilePath) : IO (Except String String) := do
  let js ← findAlphaNetRpc
  let proc ← IO.Process.output {
    cmd := "node"
    args := #[js.toString, cmd, cfgPath.toString]
  }
  if proc.exitCode == 0 then
    return .ok proc.stdout
  return .error (if proc.stderr.isEmpty then proc.stdout else proc.stderr)

private def defaultXrplOut (opts : Options) : System.FilePath :=
  if opts.outDir.toString == "build/out" then
    if opts.target == .xrpl then "build/xrpl" else "build/xrpl-alphanet"
  else opts.outDir

private unsafe def runDeploy (opts : Options) : IO UInt32 := do
  unless opts.target == .xrplAlphaNet || opts.target == .xrpl do
    IO.eprintln "pf: deploy supports --target xrpl or --target xrpl-alphanet"
    return 1
  match selectXrplNames opts.names with
  | .error reason =>
    IO.eprintln s!"pf: {reason}"
    return 1
  | .ok names =>
    if names.size != 1 then
      IO.eprintln "pf: deploy wants exactly one program"
      return 1
    let name := names[0]!
    let outDir := defaultXrplOut opts
    match ← extractXrplPrograms #[{ name := name, module := fixtureModule opts.target name }] with
    | .error reason =>
      IO.eprintln s!"pf: {reason}"
      return 1
    | .ok programs =>
      IO.FS.createDirAll outDir
      let program := programs[0]!
      let r ←
        if opts.target == .xrpl then
          ProofForge.Wasm.Xrpl.Assemble.assembleProgram outDir program
        else
          ProofForge.Wasm.Xrpl.Assemble.assembleAlphaNet outDir program
      IO.println s!"wrote {r.wasmPath}"
      let fund :=
        if opts.sendAmount.isEmpty then ""
        else ",\"send_amount_drops\":\"" ++ jsonEscape opts.sendAmount ++ "\""
      let mut fp := ""
      for m in #[program.initializer] ++ program.entries do
        if m.paramCount > 0 then
          if !fp.isEmpty then fp := fp ++ ","
          -- On-chain export is ixName (`init` → `initialize`).
          fp := fp ++ "\"" ++ jsonEscape m.ixName ++ "\":" ++ toString m.paramCount
      let params :=
        if fp.isEmpty then ""
        else ",\"function_params\":{" ++ fp ++ "}"
      let cfg :=
        "{\"rpc_url\":\"" ++ jsonEscape opts.rpcUrl ++
          "\",\"wallet_seed\":\"" ++ jsonEscape opts.wallet ++
          "\",\"wasm_path\":\"" ++ jsonEscape r.wasmPath.toString ++ "\"" ++
          fund ++ params ++ "}"
      let cfgPath ← writeTempJson cfg
      let result ← runAlphaNetJs "deploy" cfgPath
      try IO.FS.removeFile cfgPath catch _ => pure ()
      match result with
      | .error reason =>
        IO.eprintln s!"pf: deploy failed\n{reason}"
        return 1
      | .ok out =>
        IO.print out
        return 0

private def runCall (opts : Options) : IO UInt32 := do
  unless opts.target == .xrplAlphaNet || opts.target == .xrpl do
    IO.eprintln "pf: call supports --target xrpl or --target xrpl-alphanet"
    return 1
  if opts.contract.isEmpty then
    IO.eprintln "pf: call wants --contract ACCOUNT"
    return 1
  if opts.functionName.isEmpty then
    IO.eprintln "pf: call wants a function name"
    return 1
  let params :=
    if opts.callArgs.isEmpty then "[]"
    else "[" ++ String.intercalate "," (opts.callArgs.toList.map (fun a => "\"" ++ jsonEscape a ++ "\"")) ++ "]"
  let cfg :=
    "{\"rpc_url\":\"" ++ jsonEscape opts.rpcUrl ++
      "\",\"wallet_seed\":\"" ++ jsonEscape opts.wallet ++
      "\",\"contract_account\":\"" ++ jsonEscape opts.contract ++
      "\",\"function_name\":\"" ++ jsonEscape opts.functionName ++
      "\",\"parameters\":" ++ params ++ "}"
  let cfgPath ← writeTempJson cfg
  let result ← runAlphaNetJs "call" cfgPath
  try IO.FS.removeFile cfgPath catch _ => pure ()
  match result with
  | .error reason =>
    IO.eprintln s!"pf: call failed\n{reason}"
    return 1
  | .ok out =>
    IO.print out
    return 0

private def nearProgramNames : Array String :=
  Wasm.Near.Registry.names

private def selectNearNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok nearProgramNames
  else
    names.mapM fun n =>
      match nearProgramNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown near program {n}"

private unsafe def extractNearPrograms (units : Array BuildUnit) :
    IO (Except String (Array ProofForge.Wasm.Near.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := units.map fun u => ({ module := u.module } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return units.mapM fun u =>
      match Extract.extractModuleIR env u.module none >>= Wasm.Near.IR.fromExtracted with
      | .error reason => .error s!"{u.name}: {reason}"
      | .ok program =>
        if !isExamplesModule u.module then
          .ok program
        else
          let digest := Wasm.Near.IR.digestHex program
          match Wasm.Near.Registry.digestOf u.name with
          | some expected =>
            if digest == expected then .ok program
            else .error s!"{u.name}: ir/mismatch: extracted near digest {digest} != fixture {expected}"
          | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def runInit (opts : Options) : IO UInt32 := do
  if opts.initName.isEmpty then
    IO.eprintln "pf: init wants a project name"
    return 1
  let targetName? : Option String :=
    match opts.target with
    | .svm => some "svm"
    | .evm => some "evm"
    | _ => none
  let some targetName := targetName? |
    do
      IO.eprintln "pf: init supports --target svm|evm only"
      return 1
  let dst : System.FilePath := opts.initName
  if ← dst.pathExists then
    IO.eprintln s!"pf: refusing to overwrite {dst}"
    return 1
  let src : System.FilePath :=
    if targetName == "svm" then "templates/svm-counter" else "templates/evm-counter"
  if !(← src.pathExists) then
    IO.eprintln s!"pf: template missing at {src} (run from the ProofForge checkout)"
    return 1
  let proc ← IO.Process.output { cmd := "cp", args := #["-R", toString src, toString dst] }
  if proc.exitCode != 0 then
    IO.eprintln s!"pf: cp failed\n{proc.stderr}"
    return 1
  -- Rewrite template `require … from ".." / ".."` (templates/* → repo root).
  -- Sibling of the checkout → `from ".."`; otherwise absolute path to this checkout
  -- so `pf init /tmp/demo` still resolves the SDK (prod-003 temp-dir acceptance).
  let lakefile := dst / "lakefile.lean"
  if ← lakefile.pathExists then
    let repoRoot ← IO.currentDir
    let dstAbs ←
      try
        IO.FS.realPath dst
      catch _ =>
        pure (repoRoot / dst)
    let parentAbs ←
      match dstAbs.parent with
      | some p =>
        try IO.FS.realPath p catch _ => pure p
      | none => pure dstAbs
    let requireFrom :=
      if parentAbs == repoRoot then ".."
      else repoRoot.toString
    let old ← IO.FS.readFile lakefile
    let rewritten :=
      old.replace "from \"..\" / \"..\"" s!"from \"{requireFrom}\""
        |>.replace "from \"../..\"" s!"from \"{requireFrom}\""
    IO.FS.writeFile lakefile rewritten
  let tipModule := if targetName == "svm" then "MyProgram.Counter" else "MyContract.Counter"
  IO.println s!"initialized {dst} (target={targetName})"
  IO.println s!"next: cd {dst} && lake build && lake exe pf -- build --target {targetName}"
  IO.println s!"  (or: lake exe pf -- build --target {targetName} --module {tipModule})"
  return 0

private def toolLine (cmd : String) (args : Array String) (fallback : String) : IO String := do
  try
    let proc ← IO.Process.output { cmd := cmd, args := args }
    if proc.exitCode == 0 then
      let line := (trimStr proc.stdout).splitOn "\n" |>.headD (trimStr proc.stdout)
      return if line.isEmpty then fallback else line
    else
      return fallback
  catch _ =>
    return fallback

private def printVersion : IO Unit := do
  IO.println "pf 0.0.1 (ProofForge)"
  IO.println s!"lean {Lean.versionString}"
  IO.println s!"sbpf {(← toolLine "sbpf" #["--version"] "sbpf 0.2.2 (pin; binary not on PATH)")}"
  IO.println s!"solc {(← toolLine "solc" #["--version"] "0.8.34+commit.80d5c536 (pin; binary not on PATH)")}"
  IO.println s!"wat2wasm {(← toolLine "wat2wasm" #["--version"] "1.0.41 (pin; binary not on PATH)")}"
  IO.println "pins: lean v4.31.0; sbpf 0.2.2@d835bc6; solc 0.8.34; wat2wasm/wabt 1.0.41; foundry 1.7.1"

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error reason =>
    IO.eprintln s!"pf: {reason}"
    IO.eprintln usage
    return 1
  | .ok opts =>
    if opts.help then
      IO.println usage
      return 0
    if opts.version then
      printVersion
      return 0
    match opts.command with
    | .deploy => return ← runDeploy opts
    | .call => return ← runCall opts
    | .init => return ← runInit opts
    | .build =>
    let tomlUnits ← loadPfTomlUnits
    match opts.target with
    | .svm =>
      match resolveUnits opts selectSvmNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractSvmPrograms units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Svm.Assemble.assembleIRProgram opts.outDir program
            IO.println s!"wrote {r.soPath} {r.idlPath} ({r.soBytes.size} bytes)"
          return 0
    | .evm =>
      match resolveUnits opts selectEvmNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractEvmPrograms units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          let backend ← match opts.evmBackend with
            | some b => pure b
            | none => ProofForge.Evm.Assemble.backendFromEnv
          for program in programs do
            let r ← ProofForge.Evm.Assemble.assembleProgramWithBackend opts.outDir program backend
            let backendName :=
              match r.backend with
              | .solc => "solc"
              | .yulc => "yulc"
            IO.println s!"wrote {r.binPath} {r.abiPath} ({r.binHex.length / 2} bytes, {backendName})"
          return 0
    | .xrpl =>
      match resolveUnits opts selectXrplNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractXrplPrograms units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Wasm.Xrpl.Assemble.assembleProgram opts.outDir program
            IO.println s!"wrote {r.watPath} {r.wasmPath} ({r.watSource.length} bytes WAT; deployable=false)"
          return 0
    | .xrplAlphaNet =>
      match resolveUnits opts selectXrplNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractXrplPrograms units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Wasm.Xrpl.Assemble.assembleAlphaNet opts.outDir program
            IO.println s!"wrote {r.watPath} {r.wasmPath} ({r.watSource.length} bytes WAT; AlphaNet host)"
          return 0
    | .near =>
      match resolveUnits opts selectNearNames tomlUnits with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok units =>
        match ← extractNearPrograms units with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Wasm.Near.Assemble.assembleProgram opts.outDir program
            IO.println s!"wrote {r.watPath} {r.wasmPath} ({r.watSource.length} bytes WAT; deployable=false)"
          return 0

end ProofForge.Cli

unsafe def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args
