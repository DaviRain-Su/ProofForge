---
id: svm-sem-098
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-097]
---

# svm-sem-098 L3/E∞ knife 93 — Loader account-12 → account-13 skip chain

## 目标

Knife 92 completes account-12 fields after the skip chain. Emit then chains the tredecuple
skip geometry (13 dataLen reads: first block with `mov br2 br8`, 12 continuation blocks,
terminal `add 8`, final `ldx m8`) to reach the account-13 dup marker.

## 交付

1. `account12SkipNextInputMem` / `walkAccount12SkipNextAfterSkipChain?` /
   `evalWalkAccount12SkipNextAfterSkipChainToStack?` / `evalAbsAccount13Marker?`
2. Theorems：`walkAccount12SkipNextAfterSkipChain_verified`、`evalWalkAccount12_skip_next_marker_0xff`、`walkAccount12SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 93 section
- Spec guards for marker=0xBB vs abs loads; POS uses account0NonDupMarker (0xff)

## 仍未覆盖

account-13 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
