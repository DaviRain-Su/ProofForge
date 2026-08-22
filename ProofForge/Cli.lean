import ProofForge.Assemble
import ProofForge.Golden
import ProofForge.Idl
import ProofForge.IR
import ProofForge.Ops
import ProofForge.Evm.Assemble
import ProofForge.Evm.Golden
import ProofForge.Evm.IR
import ProofForge.Evm.Emit

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
    "No program names means every Golden fixture for that target.\n"

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
    | flag :: _ =>
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

private def svmSources : Array IR.Program :=
  Golden.programs.filter fun p =>
    !p.methods.any (fun m => Ops.hasEvmEffect m.ops || Ops.hasLangOp m.ops)

private def selectSvm (names : Array String) : Except String (Array IR.Program) :=
  if names.isEmpty then .ok svmSources
  else
    names.mapM fun n =>
      match svmSources.find? (·.name == n) with
      | some p => .ok p
      | none => .error s!"unknown svm program {n}"

private def selectEvm (names : Array String) : Except String (Array ProofForge.Evm.IR.Program) :=
  if names.isEmpty then .ok ProofForge.Evm.Golden.programs
  else
    names.mapM fun n =>
      match ProofForge.Evm.Golden.programs.find? (·.name == n) with
      | some p => .ok p
      | none => .error s!"unknown evm program {n}"

def run (args : List String) : IO UInt32 := do
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
      match selectSvm opts.names with
      | .error reason =>
        IO.eprintln s!"pf: {reason}"
        return 1
      | .ok programs =>
        IO.FS.createDirAll opts.outDir
        for program in programs do
          let r ← Assemble.assembleProgram opts.outDir program
          IO.println s!"wrote {r.soPath} {r.idlPath} ({r.soBytes.size} bytes)"
        return 0
    | .evm =>
      match selectEvm opts.names with
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

def main (args : List String) : IO UInt32 :=
  ProofForge.Cli.run args
