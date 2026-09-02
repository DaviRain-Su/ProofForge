import YulSemantics.BigStep
import YulSemantics.Dialect.EVM
import YulSemantics.Interp
import YulSemantics.Observation
import YulSemantics.Syntax

/-!
# CounterBridge — ProofForge Counter ↔ powdr yul-semantics (E-B4 seed)

Isolated bridge planning module (Lean v4.33, `powdr-probe/` only).

## Golden pin

ProofForge emits Counter Yul via `scripts/emit_evm_golden_yul.lean` (digest in header comment).
Audit: `python3 scripts/check_yul_fragment.py --golden`.

## PF emit → yul-semantics mapping (runtime fragment)

| ProofForge `EmitYul` | yul-semantics | Bridge status |
|---|---|---|
| `sload(slot)` | `EVM.Op.sload` | **proved** below (`counterIncrement42`) |
| `sstore(slot, v)` | `EVM.Op.sstore` | **proved** below |
| `add` / `gt` overflow guard | `EVM.Op.add`, `.gt` | planned (PF CFG `pf_pc` ladder) |
| `switch` on selector | `Stmt.switch` | planned |
| `pf_pc` interpreter loop | `for` + nested `switch` | assume (control-flow lowering) |
| `pf_store_addr20` helper | user `function` | **out of yulc verified fragment** |
| `memoryguard(n)` | builtin + scratch lowering | **assume** (yulc desugars) |
| ctor `code` object | `YulSemantics.Object` | **assume** (deployment wrapper) |
| `call` / `delegatecall` | open-world `ExternalsRealized` | **explicit non-goal** |

## Unproved assumptions (audit boundary)

See `counterBridgeAssumptions` — documentation until P3 lemmas land.
-/

namespace ProofForgePowdrProbe

open YulSemantics EVM

/-- Digest from `// digest=…` in golden Counter emit (`emit_evm_golden_yul.lean`). -/
def counterGoldenDigest : String := "254202356ee921d6"

/-- Audit checklist (documentation strings; formal Prop bundle is P3). -/
def counterBridgeAssumptions : List String := [
  "PF deployment object wrapper (ctor codecopy/return) not modeled in this slice",
  "PF `pf_store_addr20` / `pf_store_fixed_bytes` helpers treated as user functions outside yulc opTable",
  "`memoryguard` reservation invisible to raw `msize` (yulc lowering assumption)",
  "No `gas()` oracle — yul-semantics omits gas (Feature A solc path may still emit gas())",
  "Open-world `call`/`create` require `ExternalsRealized` (Counter runtime has none)",
  "Full selector dispatch + `pf_pc` CFG ladder not yet linked to `RunCommitted`"
]

/-- Core Counter increment: `sstore(0, add(sload(0), 42))` (PF `increment` happy-path body). -/
def counterIncrement42 : Block Op := yul% {
  sstore(0, add(sload(0), 42))
}

/-- Starting from slot `0 = 0`, increment by `42` commits storage `42`. -/
example :
    (Interp.run EVM.exec 200 counterIncrement42 EvmState.init).map (·.2.1.storage 0)
      = .ok 42 := by native_decide

/-- PF `get` when counter ≠ 0 returns `sload(0)` via `mstore`+`return` (simplified). -/
def counterGetCore : Block Op := yul% {
  mstore(0, sload(0))
  return(0, 32)
}

/-- Chained increment-then-read leaves storage at `42`. -/
def counterIncrementThenGet : Block Op := yul% {
  sstore(0, add(sload(0), 42))
  mstore(0, sload(0))
  return(0, 32)
}

example :
    (Interp.run EVM.exec 200 counterIncrementThenGet EvmState.init).map (·.2.1.storage 0)
      = .ok 42 := by native_decide

/-- Empty program `RunCommitted` is reachable (Observation import smoke). -/
example : RunCommitted ([] : Block Op) EvmState.init [] EvmState.init .normal := by
  refine ⟨EvmState.init, Step.block (D := evm) Step.seqNil, rfl⟩

#guard counterGoldenDigest.length = 16
#guard counterBridgeAssumptions.length ≥ 5
#guard counterIncrement42.length = 1

end ProofForgePowdrProbe
