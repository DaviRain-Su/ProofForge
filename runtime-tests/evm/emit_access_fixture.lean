import ProofForge
import Examples.TwoStepCounter
import Examples.Credits

/-!
Dedicated EVM-SDK-1 assembly fixture (not part of any lake target; coordinator owns
`Evm.Golden` / `Evm.Registry` wiring).

Extracts the two `Access` consumers with the same live pipeline the `pf` CLI uses
(`Extract.extractModuleIR` → `Evm.IR.fromExtracted` → `Evm.Assemble.assembleProgram`)
and writes `Name.yul` / `Name.abi.json` / `Name.bin` into the output directory. The
programs are deliberately not registered, so no digest gate applies here.

Usage:
  lake env lean --run runtime-tests/evm/emit_access_fixture.lean [outDir]
-/

unsafe def main (args : List String) : IO UInt32 := do
  let args := args.dropWhile (· == "--")
  let outDir :=
    match args with
    | outDir :: _ => System.FilePath.mk outDir
    | [] => System.FilePath.mk "build/evm"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let namespaces := #[`Examples.TwoStepCounter, `Examples.Credits]
  let modules := namespaces.map fun ns => ({ module := ns } : Lean.Import)
  let env ← Lean.importModules modules {} (loadExts := true)
  for ns in namespaces do
    match ProofForge.Extract.extractModuleIR env ns none >>=
        ProofForge.Evm.IR.fromExtracted with
    | .error reason =>
      IO.eprintln s!"emit-access-fixture: {ns}: {reason}"
      return 1
    | .ok program =>
      let r ← ProofForge.Evm.Assemble.assembleProgram outDir program
      IO.println s!"wrote {r.yulPath} {r.abiPath} {r.binPath} ({r.binHex.length / 2} bytes)"
  return 0
