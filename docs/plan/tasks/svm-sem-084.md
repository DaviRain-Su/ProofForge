---
id: svm-sem-084
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-083]
---

# svm-sem-084 L3/E∞ knife 79 — Loader account-10 → account-11 skip chain

## 目标

在 account-10 executable/rent 齐备之后，覆盖 Emit 从 account-10 header 游标链式
`emitSkipAccount` 到 account-11 dup marker。同一 undecuple（11-read）skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account10SkipNextInputMem` / `walkAccount10SkipNextAfterSkipChain?` /
   `evalWalkAccount10SkipNextAfterSkipChainToStack?` / `evalAbsAccount11Marker?`
2. Theorems：`walkAccount10SkipNextAfterSkipChain_verified`、`evalWalkAccount10_skip_next_marker_0xff`、`walkAccount10SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 79 section
- Spec guards for marker=0xff / marker=0xB9 vs abs loads

## 仍未覆盖

account-11 meta/field knives。
