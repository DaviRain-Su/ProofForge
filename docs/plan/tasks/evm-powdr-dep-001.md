---
id: evm-powdr-dep-001
scope: evm
status: partial
depends-on: []
updated: 2026-09-01
---

# evm-powdr-dep-001 — Pin powdr-labs semantics as optional Lake deps

## Objective

Add optional Lake git dependencies on [powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics),
[yul-semantics](https://github.com/powdr-labs/yul-semantics), and [yul-compiler](https://github.com/powdr-labs/yul-compiler)
for EVM Feature B, without pulling them into the default `ProofForge` / CI build graph.

## Attempt (2026-09-01)

- Pinned `evm-semantics` @ `2f8714d6ba960a3de67720019b54513f5bc1a2e3` (HEAD at probe time).
- Initial probe pulled Mathlib at Lean **v4.33.0** while ProofForge pins **v4.31.0** — blocked main graph.
- **Update:** upstream `evm-semantics` @ same pin is now **Mathlib-free** (Batteries v4.33 only).

## Isolated probe (landed)

- `powdr-probe/` — separate Lake package on Lean v4.33, `require evm_semantics` @ pin above.
- `scripts/build_powdr_probe.sh` → `lake build ProofForgePowdrProbe` (does not build root `ProofForge`).
- Smoke: `ProofForgePowdrProbe.Basic` imports `EvmSemantics.EVM.State` + `EvmSemantics.Operation`.

## Still open

- Pin `yul-semantics` + `yul-compiler` in the same isolated package (or sibling).
- Optional CI lane invoking `scripts/build_powdr_probe.sh`.
- Feature B integration design (Yul backend path vs L3 refinement) — see `multi-target-strategy.md` §2.

## Acceptance (remaining)

- `yul-semantics` + `yul-compiler` build in isolated probe without main-graph regression.
- CI optional lane documented; default lanes unchanged.
