---
id: evm-powdr-dep-001
scope: evm
status: partial
depends-on: []
updated: 2026-09-01
---

# evm-powdr-dep-001 — Pin powdr-labs semantics as optional Lake deps

## Objective

Add optional Lake git dependencies on [evm-semantics](https://github.com/powdr-labs/evm-semantics),
[yul-semantics](https://github.com/powdr-labs/yul-semantics), and [yul-compiler](https://github.com/powdr-labs/yul-compiler)
for EVM Feature B, without pulling them into the default `ProofForge` / CI build graph.

## Attempt (2026-09-01)

- Pinned `evm-semantics` @ `2f8714d6ba960a3de67720019b54513f5bc1a2e3` (HEAD at probe time).
- Initial probe pulled Mathlib at Lean **v4.33.0** while ProofForge pins **v4.31.0** — blocked main graph.
- **Update:** upstream `evm-semantics` @ same pin is now **Mathlib-free** (Batteries v4.33 only).

## Isolated probe (landed)

| Repo | Pin | Smoke module |
|---|---|---|
| evm-semantics | `2f8714d6…` | `ProofForgePowdrProbe.Basic` |
| yul-semantics | `c9914c13…` | `ProofForgePowdrProbe.YulSemanticsSmoke` |
| yul-compiler | `c2e44cd2…` | `ProofForgePowdrProbe.YulCompilerSmoke` (optional `--full`) |

- `powdr-probe/` — separate Lake package on Lean v4.33.
- `scripts/build_powdr_probe.sh` — fast: evm + yul-semantics; `--full` adds yul-compiler (+ Mathlib v4.33).
- Does **not** build root `ProofForge`.

## Still open

- Optional CI lane invoking `scripts/build_powdr_probe.sh [--full]`.
- Feature B integration design (Yul backend path vs L3 refinement) — see `multi-target-strategy.md` §2.
- **E-B1** fragment audit landed (`evm-yul-fragment-001`); E-B2 yulc backend next.

## Acceptance (remaining)

- CI optional lane documented and wired; default lanes unchanged.
