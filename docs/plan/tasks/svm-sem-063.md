---
id: svm-sem-063
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-062]
---

# svm-sem-063 L3/E∞ knife 58 — Loader account-7 → account-8 skip chain

## 目标

在 account-7 executable/rent 齐备之后，覆盖 Emit 从 account-7 header 游标链式
`emitSkipAccount` 到 account-8 dup marker。同一 octuple skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account7SkipNextInputMem` / `walkAccount7SkipNextAfterSkipChain?` /
   `evalWalkAccount7SkipNextAfterSkipChainToStack?` / `evalAbsAccount8Marker?`
2. Theorems：`walkAccount7SkipNextAfterSkipChain_verified`、
   `evalWalkAccount7_skip_next_marker_0xff`、
   `walkAccount7SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 58 section
- Spec guards for marker=0xff / 0xB3 vs abs loads

## 仍未覆盖

account-8 meta/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
