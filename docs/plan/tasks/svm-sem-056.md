---
id: svm-sem-056
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-055]
---

# svm-sem-056 L3/E∞ knife 51 — Loader account-6 → account-7 skip chain

## 目标

在 account-6 executable/rent 齐备之后，覆盖 Emit 从 account-6 header 游标链式
`emitSkipAccount` 到 account-7 dup marker。同一 septuple skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account6SkipNextInputMem` / `walkAccount6SkipNextAfterSkipChain?` /
   `evalWalkAccount6SkipNextAfterSkipChainToStack?` / `evalAbsAccount7Marker?`
2. Theorems：`walkAccount6SkipNextAfterSkipChain_verified`、
   `evalWalkAccount6_skip_next_marker_0xff`、
   `walkAccount6SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 51 section
- Spec guards for marker=0xff / 0xB2 vs abs loads

## 仍未覆盖

account-7 meta/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
