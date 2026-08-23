import Lean
import ProofForge.Golden
import ProofForge.Extract
import ProofForge.Core.IR
import ProofForge.Svm.Assemble
import ProofForge.Evm.Assemble
import ProofForge.Evm.Golden
import ProofForge.Evm.IR

namespace ProofForge.Cli

inductive Target where
  | svm
  | evm
  deriving BEq, Repr, Inhabited

def parseTarget : String → Option Target
  | "svm" | "solana" | "sbpf" => some .svm
  | "evm" => some .evm
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
    "  pf build --target <svm|evm> [--out DIR] [Program ...]\n" ++
    "\n" ++
    "svm  writes Name.so / Name.s / Name.idl.json\n" ++
    "evm  writes Name.bin / Name.yul / Name.abi.json\n" ++
    "No program names means every registered source module for the selected target.\n"

private def parseArgs (args : List String) : Except String Options :=
  let rec go (rest : List String) (o : Options) : Except String Options :=
    match rest with
    | [] => .ok o
    | "-h" :: _ | "--help" :: _ => .ok { o with help := true }
    | "--target" :: t :: rest =>
      match parseTarget t with
      | some tgt => go rest { o with target := tgt }
      | none => .error s!"unknown target {t}"
    | "--out" :: d :: rest => go rest { o with outDir := d }
    | flag :: rest =>
      if flag.startsWith "-" then .error s!"unknown flag {flag}"
      else
        let names := rest.foldl (init := #[flag]) fun acc a =>
          if a.startsWith "-" then acc else acc.push a
        .ok { o with names }
  let args := args.dropWhile (· == "--")
  let args :=
    match args with
    | "build" :: rest => rest
    | rest => rest
  go args {}

private def svmFixtureNames : Array String :=
  Golden.programs.filterMap fun program =>
    match Svm.IR.fromProgram program with
    | .ok _ => some program.name
    | .error _ => none

private def selectSvmNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok svmFixtureNames
  else
    names.mapM fun n =>
      match svmFixtureNames.find? (· == n) with
      | some _ => .ok n
      | none => .error s!"unknown svm program {n}"

private def svmModuleName (name : String) : Lean.Name :=
  if name == "Phoenix" then `Projects.Phoenix
  else Lean.Name.str `Examples name

/--
CLI 构建必须重新从用户模块抽 IR，不能组装 `Golden` smoke fixture。Golden 只负责
列出可构建模块并钉 canonical digest。
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
        match Golden.digestOf name with
        | some expected =>
          if digest == expected then .ok program
          else .error s!"{name}: ir/mismatch: extracted digest != fixture"
        | none => .ok program
  catch e =>
    return .error s!"source import failed: {e}"

private def evmFixtureNames : Array String :=
  ProofForge.Evm.Golden.programs.map (·.name)

private def selectEvmNames (names : Array String) : Except String (Array String) :=
  if names.isEmpty then .ok evmFixtureNames
  else
    names.mapM fun n =>
      match evmFixtureNames.find? (· == n) with
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
        match Evm.Golden.digestOf name with
        | some expected =>
          if digest == expected then .ok program
          else .error s!"{name}: ir/mismatch: extracted evm digest != fixture"
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

end ProofForge.Cli

unsafe def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args
