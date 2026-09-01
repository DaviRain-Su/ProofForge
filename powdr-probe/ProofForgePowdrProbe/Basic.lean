import EvmSemantics.EVM.State
import EvmSemantics.EVM.Operation

/-!
Isolated import smoke for powdr-labs EVM Feature B planning (E-B0).

This library lives under `powdr-probe/` with Lean v4.33 and must not be added
to the root `lakefile.lean` default targets.
-/

namespace ProofForgePowdrProbe

/-- Public EVM machine state type is reachable from the pinned semantics. -/
abbrev smokeState := EvmSemantics.EVM.State

/-- Opcode algebra is linked through the same dependency closure. -/
abbrev smokeOp := EvmSemantics.Operation

end ProofForgePowdrProbe
