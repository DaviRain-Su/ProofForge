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

namespace ProofForge.Cli

/-- A target names one concrete chain. `wasm` is a chain family, not a target: it is
rejected with a hint so callers pick a member (e.g. `xrpl`). -/
inductive Target where
  | svm
  | evm
  | xrpl
  | xrplAlphaNet
  deriving BEq, Repr, Inhabited

def parseTarget : String → Option Target
  | "svm" | "solana" | "sbpf" => some .svm
  | "evm" => some .evm
  | "xrpl" | "xrpl-bedrock" | "bedrock" => some .xrpl
  | "xrpl-alphanet" | "alphanet" => some .xrplAlphaNet
  | _ => none

inductive Command where
  | build
  | deploy
  | call
  deriving BEq, Repr, Inhabited

structure Options where
  command : Command := .build
  target : Target := .svm
  outDir : System.FilePath := "build/out"
  names : Array String := #[]
  rpcUrl : String := "https://alphanet.xrpl.org"
  wallet : String := "snoPBrXtMeMyMHUVTgbuqAfg1SUTb"
  contract : String := ""
  functionName : String := ""
  callArgs : Array String := #[]
  /-- Create-time tfSendAmount drops. Empty = no InstanceParameterValues. -/
  sendAmount : String := ""
  help : Bool := false

private def usage : String :=
  "pf — ProofForge compiler\n" ++
    "\n" ++
    "Usage:\n" ++
    "  pf build --target <svm|evm|xrpl|xrpl-alphanet> [--out DIR] [Program ...]\n" ++
    "  pf deploy --target <xrpl|xrpl-alphanet> [--out DIR] [--rpc URL] [--wallet SEED] [--send-amount DROPS] Program\n" ++
    "  pf call --target <xrpl|xrpl-alphanet> --contract ACCOUNT [--rpc URL] [--wallet SEED] Function [UINT64 ...]\n" ++
    "\n" ++
    "svm  writes Name.so / Name.s / Name.idl.json\n" ++
    "evm  writes Name.bin / Name.yul / Name.abi.json\n" ++
    "xrpl writes Name.wat / Name.wasm (XRPL Bedrock local; locked wat2wasm)\n" ++
    "xrpl-alphanet same IR, XLS-0102 host names for live AlphaNet\n" ++
    "deploy/call talk via runtime-tests/xrpl/alphanet-rpc.js.\n" ++
    "     --target xrpl = Bedrock/get_* names (local 2.6.1). xrpl-alphanet = XLS-0102.\n" ++
    "     --send-amount funds the pseudo-account (local 2.6.1 first-install only).\n" ++
    "     Public 3.3.0: Function ABI + increment(1) live; do not call initialize(0).\n" ++
    "     wasm is a chain family, not a target; pick a member such as xrpl\n" ++
    "No program names on build means every registered source module.\n"

def parseArgs (args : List String) : Except String Options :=
  let rec go (rest : List String) (o : Options) : Except String Options :=
    match rest with
    | [] => .ok o
    | "-h" :: _ | "--help" :: _ => .ok { o with help := true }
    | "--target" :: t :: rest =>
      match parseTarget t with
      | some tgt => go rest { o with target := tgt }
      | none =>
          if t == "wasm" then
            .error "wasm is a chain family, not a target; pick a concrete member (e.g. xrpl)"
          else .error s!"unknown target {t}"
    | "--out" :: d :: rest => go rest { o with outDir := d }
    | "--rpc" :: u :: rest => go rest { o with rpcUrl := u }
    | "--wallet" :: s :: rest => go rest { o with wallet := s }
    | "--contract" :: a :: rest => go rest { o with contract := a }
    | "--send-amount" :: d :: rest => go rest { o with sendAmount := d }
    | flag :: rest =>
      if flag.startsWith "-" then .error s!"unknown flag {flag}"
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
    | rest => (Command.build, rest)
  let start : Options :=
    match cmd with
    | .deploy | .call => { command := cmd, target := .xrplAlphaNet }
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

def svmModuleName (name : String) : Lean.Name :=
  Lean.Name.str `Examples name

/--
CLI 构建必须重新从用户模块抽 IR，不能组装 legacy Golden smoke fixture。target registry
只负责列出可构建模块并钉 canonical digest。
-/
private unsafe def extractSvmPrograms (names : Array String) :
    IO (Except String (Array Svm.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let modules := names.map fun name => ({ module := svmModuleName name } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return names.mapM fun name =>
      let ns := svmModuleName name
      match Extract.extractModuleIR env ns none >>= Svm.IR.fromExtracted with
      | .error reason => .error s!"{name}: {reason}"
      | .ok program =>
        let digest := Svm.IR.digestHex program
        match Svm.Registry.digestOf name with
        | some expected =>
          if digest == expected then .ok program
          else .error s!"{name}: ir/mismatch: extracted digest {digest} != fixture {expected}"
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

private unsafe def extractEvmPrograms (names : Array String) :
    IO (Except String (Array ProofForge.Evm.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let moduleName (name : String) := Lean.Name.str `Examples name
    let modules := names.map fun name => ({ module := moduleName name } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return names.mapM fun name =>
      match Extract.extractModuleIR env (moduleName name) none >>= Evm.IR.fromExtracted with
      | .error reason => .error s!"{name}: {reason}"
      | .ok program =>
        let digest := Evm.IR.digestHex program
        match Evm.Registry.digestOf name with
        | some expected =>
          if digest == expected then .ok program
          else .error s!"{name}: ir/mismatch: extracted evm digest {digest} != fixture {expected}"
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

private unsafe def extractXrplPrograms (names : Array String) :
    IO (Except String (Array ProofForge.Wasm.Xrpl.IR.Program)) :=
  try
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let moduleName (name : String) := Lean.Name.str `Examples name
    let modules := names.map fun name => ({ module := moduleName name } : Lean.Import)
    let env ← Lean.importModules modules {} (loadExts := true)
    return names.mapM fun name =>
      match Extract.extractModuleIR env (moduleName name) none >>= Wasm.Xrpl.IR.fromExtracted with
      | .error reason => .error s!"{name}: {reason}"
      | .ok program =>
        let digest := Wasm.Xrpl.IR.digestHex program
        match Wasm.Xrpl.Registry.digestOf name with
        | some expected =>
            if digest == expected then .ok program
            else .error s!"{name}: ir/mismatch: extracted xrpl digest {digest} != fixture {expected}"
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
    match ← extractXrplPrograms #[name] with
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
    match opts.command with
    | .deploy => return ← runDeploy opts
    | .call => return ← runCall opts
    | .build =>
    match opts.target with
    | .svm =>
      match selectSvmNames opts.names with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok names =>
        match ← extractSvmPrograms names with
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
      match selectEvmNames opts.names with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok names =>
        match ← extractEvmPrograms names with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Evm.Assemble.assembleProgram opts.outDir program
            IO.println s!"wrote {r.binPath} {r.abiPath} ({r.binHex.length / 2} bytes)"
          return 0
    | .xrpl =>
      match selectXrplNames opts.names with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok names =>
        match ← extractXrplPrograms names with
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
      match selectXrplNames opts.names with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok names =>
        match ← extractXrplPrograms names with
        | .error reason =>
          IO.eprintln s!"pf: {reason}"
          return 1
        | .ok programs =>
          IO.FS.createDirAll opts.outDir
          for program in programs do
            let r ← ProofForge.Wasm.Xrpl.Assemble.assembleAlphaNet opts.outDir program
            IO.println s!"wrote {r.watPath} {r.wasmPath} ({r.watSource.length} bytes WAT; AlphaNet host)"
          return 0

end ProofForge.Cli

unsafe def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args
