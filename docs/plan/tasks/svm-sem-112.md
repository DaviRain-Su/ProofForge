---
id: svm-sem-112
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-111]
---

# svm-sem-112 L3/E∞ knife 107 — Loader account-14 → account-15 skip chain

## 目标

Knife 106 completes account-14 fields after the skip chain. Emit chains the quindecuple skip geometry (15 dataLen reads: first block with `mov br2 br8`, 14 continuation blocks, terminal `add 8`, final `ldx m8`) to reach the account-15 dup marker.

## 交付

1. `account14SkipNextInputMem` / `walkAccount14SkipNextAfterSkipChain?` /
   `evalWalkAccount14SkipNextAfterSkipChainToStack?` / `evalAbsAccount15Marker?`
2. Theorems：`walkAccount14SkipNextAfterSkipChain_verified`、`evalWalkAccount14_skip_next_marker_0xff`、`walkAccount14SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 107 section
- Spec guards for marker=0xBD vs abs loads; POS uses account0NonDupMarker (0xff)

## 仍未覆盖

account-15 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
