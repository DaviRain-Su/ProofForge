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

## Delivered (Counter seed)

| Gate | Script |
|---|---|
| Compile smoke | `scripts/smoke_yulc_counter.sh` |
| Anvil behavior diff | `runtime-tests/evm/anvil_yulc_counter.sh` |
| Runner | `runtime-tests/evm/yulc.sh` |

**Counter evidence (2026-09-01):** bytecode differs (solc 1694 vs yulc 2426 hex chars) but
ctor/increment/get storage behavior matches on Anvil.

## Known rejections (no dual-backend yet)

| Fixture | Blocker |
|---|---|
| Token, Vault, TipJar | `gas()` in call paths (R1) |
| Wide | may compile; not in Anvil ladder yet |

## Still open

- Expand ladder: Capped, Ownable (immutables caveat), Const
- CI optional job `evm-yulc` with yul-compiler Mathlib cache
- Fragment allowlist table in manifest

## Acceptance

- [x] Counter dual-backend Anvil gate green locally
- [ ] CI optional lane green with cached `build_yulc.sh`
- [ ] ≥3 fixtures on behavior-diff allowlist
