---
id: svm-sem-049
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-048]
---

# svm-sem-049 L3/E∞ knife 44 — Loader account-5 → account-6 skip chain

## 目标

在 account-5 executable/rent 齐备之后，覆盖 Emit 从 account-5 header 游标链式
`emitSkipAccount` 到 account-6 dup marker。同一 sextuple skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account5SkipNextInputMem` / `walkAccount5SkipNextAfterSkipChain?` /
   `evalWalkAccount5SkipNextAfterSkipChainToStack?` / `evalAbsAccount6Marker?`
2. Theorems：`walkAccount5SkipNextAfterSkipChain_verified`、
   `evalWalkAccount5_skip_next_marker_0xff`、
   `walkAccount5SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 44 section
- Spec guards for marker=0xff / 0xB0 vs abs loads

## 仍未覆盖

account-6 meta/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
