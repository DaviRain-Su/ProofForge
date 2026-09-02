---
id: svm-sem-105
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-104]
---

# svm-sem-105 L3/E∞ knife 100 — Loader account-13 → account-14 skip chain

## 目标

Knife 99 completes account-13 fields after the skip chain. Emit then chains the quattuordecuple
skip geometry (14 dataLen reads: first block with `mov br2 br8`, 13 continuation blocks,
terminal `add 8`, final `ldx m8`) to reach the account-14 dup marker.

## 交付

1. `account13SkipNextInputMem` / `walkAccount13SkipNextAfterSkipChain?` /
   `evalWalkAccount13SkipNextAfterSkipChainToStack?` / `evalAbsAccount14Marker?`
2. Theorems：`walkAccount13SkipNextAfterSkipChain_verified`、`evalWalkAccount13_skip_next_marker_0xff`、`walkAccount13SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 100 section
- Spec guards for marker=0xBC vs abs loads; POS uses account0NonDupMarker (0xff)

## 仍未覆盖

account-14 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
