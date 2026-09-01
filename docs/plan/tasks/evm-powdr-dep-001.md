---
id: evm-powdr-dep-001
scope: evm
status: blocked
depends-on: []
---

# evm-powdr-dep-001 — Pin powdr-labs semantics as optional Lake deps

## Objective

Add optional Lake git dependencies on [powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics),
[yul-semantics](https://github.com/powdr-labs/yul-semantics), and [yul-compiler](https://github.com/powdr-labs/yul-compiler)
for EVM Feature B, without pulling them into the default `ProofForge` / CI build graph.

## Attempt (2026-09-01)

- Pinned `evm-semantics` @ `2f8714d6ba960a3de67720019b54513f5bc1a2e3` (HEAD at probe time).
- `lake update` pulled Mathlib at Lean **v4.33.0** while ProofForge pins **v4.31.0**.
- Main `lake build ProofForge` failed (`Mathlib.Tactic.Linter.Style`, `TokenTlv` rebuild breakage).

## Blocker

Toolchain / Mathlib revision mismatch between ProofForge pin and powdr-labs transitive Mathlib.

## Unblock options

1. **Isolated package**: separate `lakefile.powdr.lean` + dedicated CI job on matching toolchain (may require bumping ProofForge to v4.33+ globally).
2. **Vendor subset**: copy only needed lemma files (not desired long-term).
3. **Upstream alignment**: wait for powdr to pin same Mathlib revision as ProofForge, or bump ProofForge toolchain in a dedicated migration PR first.

## Acceptance (when unblocked)

- `lake build ProofForgePowdrProbe` succeeds without building default `ProofForge`.
- CI optional lane documents probe command; default lanes unchanged.
