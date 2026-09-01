---
id: evm-yulc-diff-001
scope: evm
status: partial
depends-on: [evm-yulc-backend-001]
updated: 2026-09-01
---

# evm-yulc-diff-001 — Dual-backend Anvil differential (solc vs yulc)

## Objective

Regression-test that yulc-assembled bytecode matches solc **behavior** (not bytes) on
Anvil for fixtures inside the verified fragment.

## Delivered

| Gate | Script |
|---|---|
| Shared helpers | `runtime-tests/evm/lib_yulc.sh` |
| Compile smoke | `scripts/smoke_yulc_counter.sh` |
| Compile matrix | `scripts/check_yulc_compile_matrix.py` |
| Anvil behavior diff (Counter) | `runtime-tests/evm/anvil_yulc_counter.sh` |
| Anvil behavior diff (Capped) | `runtime-tests/evm/anvil_yulc_capped.sh` |
| Anvil behavior diff (Const) | `runtime-tests/evm/anvil_yulc_const.sh` |
| Anvil behavior diff (Flag) | `runtime-tests/evm/anvil_yulc_flag.sh` |
| Anvil behavior diff (Phase) | `runtime-tests/evm/anvil_yulc_phase.sh` |
| Runner | `runtime-tests/evm/yulc.sh` |

**Counter evidence (2026-09-01):** bytecode differs (solc 1694 vs yulc 2426 hex chars) but
ctor/increment/get storage behavior matches on Anvil.

**Capped evidence (2026-09-01):** bytecode differs (solc 5562 vs yulc 17328 hex chars) but
dual-backend behavior matches on Anvil.

**Const evidence (2026-09-01):** bytecode differs (solc 2018 vs yulc 5862 hex chars) but
immutable ctor fields and touch behavior match on Anvil.

**Flag evidence (2026-09-01):** bytecode differs but u8 mask + count behavior matches on Anvil.

**Phase evidence (2026-09-01):** bytecode differs (solc 570 vs yulc 1046 hex chars) but
idle/live tag transitions match on Anvil.

**Compile matrix (2026-09-01):** 7/10 registry programs accept yulc (Counter, Capped, Const,
Wide, Flag, Phase, TipJar). Ownable/Token/Vault reject on fragment.

## Known rejections (no dual-backend yet)

| Fixture | Blocker |
|---|---|
| Ownable | fragment (immutables / Ownable pattern) |
| Token, Vault | `gas()` in call paths (R1) |

## Still open

- Expand ladder: Wide, TipJar
- CI optional job `evm-yulc` with yul-compiler Mathlib cache
- Fragment allowlist table in manifest

## Acceptance

- [x] Counter dual-backend Anvil gate green locally
- [x] Capped dual-backend Anvil gate green locally
- [x] Const dual-backend Anvil gate green locally
- [x] Flag dual-backend Anvil gate green locally
- [x] Phase dual-backend Anvil gate green locally
- [ ] CI optional lane green with cached `build_yulc.sh`
- [x] ≥3 fixtures on behavior-diff allowlist (Counter, Capped, Const)
