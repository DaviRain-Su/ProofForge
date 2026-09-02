---
id: svm-sem-077
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-076]
---

# svm-sem-077 L3/E∞ knife 72 — Loader account-9 → account-10 skip chain

## 目标

在 account-9 executable/rent 齐备之后，覆盖 Emit 从 account-9 header 游标链式
`emitSkipAccount` 到 account-10 dup marker。同一 decuple skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account9SkipNextInputMem` / `walkAccount9SkipNextAfterSkipChain?` /
   `evalWalkAccount9SkipNextAfterSkipChainToStack?` / `evalAbsAccount10Marker?`
2. Theorems：`walkAccount9SkipNextAfterSkipChain_verified`、
   `evalWalkAccount9_skip_next_marker_0xff`、
   `walkAccount9SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 72 section
- Spec guards for marker=0xff / 0xB7 vs abs loads

## 仍未覆盖

account-10 meta/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
