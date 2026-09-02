---
id: evm-l3-bridge-001
scope: evm
status: partial
depends-on: [evm-yul-fragment-001, evm-yulc-backend-001]
updated: 2026-09-02
---

# evm-l3-bridge-001 — Emit fragment ↔ powdr L3 semantics bridge (Counter-level)

## Objective

Establish a **bounded correspondence** between ProofForge `EmitYul` output and powdr-labs
`yul-semantics` `RunCommitted` / `evm-semantics` `Steps` for a Counter-scale fixture —
mirroring SVM `svm-sem-*` evidence style.

## Scope

| In scope | Out of scope |
|---|---|
| Counter (or Const) golden Yul fragment | Full Anvil 41/41 conformance |
| Documented assume/audit boundary for externals | Replacing solc default backend |
| Isolated `powdr-probe/` Lake target | Vendor powdr into `ProofForge/Evm/*` |
| `assume`-backed or partial Lean lemmas | Claiming Lean theorem ⇒ mainnet correctness |

## Deliverables

1. **Task scaffold** (this file) with acceptance checklist
2. **Golden fragment pin** — reuse `emit_evm_golden_yul.lean` / `check_yul_fragment.py` output
3. **Probe module** — `powdr-probe/CounterBridge.lean` importing yul-semantics types only
4. **Statement sketch** — e.g. `CounterYul ⊆ VerifiedFragment` + `RunCommitted` stepping plan
5. **CI** — optional `powdr-probe` build lane (no Mathlib cache on main Lean lane)

## Phases

| Phase | Content | Acceptance |
|---|---|---|
| P0 | Pin golden Yul + fragment audit table | `check_yul_fragment.py` green on Counter |
| P1 | Import yul-semantics `RunCommitted` in probe | **partial ✓** — `CounterBridge.lean` + `build_powdr_probe.sh` |
| P2 | Counter ctor/increment/get opcode trace map | **partial ✓** — mapping table + `counterIncrement42` interp proof |
| P3 | Bounded lemma or explicit `assume` list | Reviewable boundary in task + probe README |

## Dependencies

- E-B0: `powdr-probe/` + `scripts/build_powdr_probe.sh`
- E-B1: `scripts/check_yul_fragment.py`
- E-B2: `pf build --backend yulc` smoke

## Acceptance

- [x] `powdr-probe/ProofForgePowdrProbe/CounterBridge.lean` builds in isolated target
- [x] Golden Counter Yul digest pinned (`254202356ee921d6` in probe + `emit_evm_golden_yul.lean`)
- [x] Documented mapping: PF emit names ↔ yul-semantics constructs (sload/sstore/increment/get)
- [x] Explicit list of unproved assumptions (`counterBridgeAssumptions`)
- [ ] `RunCommitted` lemma for full PF selector/`pf_pc` ladder
- [ ] Optional CI job does not block main `lake build`

## Non-goals

- Full yul-compiler optimization pipeline equivalence
- gas() modeling (yul-semantics intentionally omits gas)
- Replacing Feature A solc path
