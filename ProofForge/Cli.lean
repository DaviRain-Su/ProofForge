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

structure Options where
  target : Target := .svm
  outDir : System.FilePath := "build/out"
  names : Array String := #[]
  help : Bool := false

private def usage : String :=
  "pf — ProofForge compiler\n" ++
    "\n" ++
    "Usage:\n" ++
    "  pf build --target <svm|evm|xrpl|xrpl-alphanet> [--out DIR] [Program ...]\n" ++
    "\n" ++
    "svm  writes Name.so / Name.s / Name.idl.json\n" ++
    "evm  writes Name.bin / Name.yul / Name.abi.json\n" ++
    "xrpl writes Name.wat / Name.wasm (XRPL Bedrock local; locked wat2wasm)\n" ++
    "xrpl-alphanet same IR, XLS-0102 host names for live AlphaNet\n" ++
    "     wasm is a chain family, not a target; pick a member such as xrpl\n" ++
    "No program names means every registered source module for the selected target.\n"

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
    | flag :: rest =>
      if flag.startsWith "-" then .error s!"unknown flag {flag}"
      else go rest { o with names := o.names.push flag }
  let args := args.dropWhile (· == "--")
  let args :=
    match args with
    | "build" :: rest => rest
    | rest => rest
  go args {}

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
