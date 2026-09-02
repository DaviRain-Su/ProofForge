import YulParser.Core

/-!
Smoke import for powdr-labs/yul-compiler parser surface (Feature B verified backend).
Pulls Mathlib v4.33 transitively — build via `ProofForgePowdrProbeFull` / `--full`.
-/

namespace ProofForgePowdrProbe

abbrev smokeYulParser := YulParser.Parser

end ProofForgePowdrProbe
