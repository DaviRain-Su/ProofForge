import ProofForge.Evm.Emit
import ProofForge.Evm.Golden
import ProofForge.Evm.IR

/-!
Emit golden EVM Yul for `scripts/check_yul_fragment.py --golden`.

Usage: `lake env lean --run scripts/emit_evm_golden_yul.lean`
Each program is delimited by `--- name ---` on its own line.
-/

open ProofForge

structure GoldenFixture where
  name : String
  emit : Except String String

def counterYul : Except String String := do
  let p ← Evm.IR.fromProgram Golden.extractedCounter
  Evm.Emit.emitYul p

def goldenFixtures : Array GoldenFixture := #[
  { name := "Counter", emit := counterYul },
  { name := "Token", emit := Evm.Emit.emitYul Evm.Golden.extractedToken },
  { name := "Ownable", emit := Evm.Emit.emitYul Evm.Golden.extractedOwnable },
  { name := "TipJar", emit := Evm.Emit.emitYul Evm.Golden.extractedTipJar },
  { name := "Vault", emit := Evm.Emit.emitYul Evm.Golden.extractedVault },
  { name := "Capped", emit := Evm.Emit.emitYul Evm.Golden.extractedCapped },
  { name := "Const", emit := Evm.Emit.emitYul Evm.Golden.extractedConst },
  { name := "Wide", emit := Evm.Emit.emitYul Evm.Golden.extractedWide }
]

def main : IO Unit := do
  for fx in goldenFixtures do
    IO.println s!"--- {fx.name} ---"
    match fx.emit with
    | .error reason => IO.println s!"// emit error: {reason}"
    | .ok yul => IO.print yul
