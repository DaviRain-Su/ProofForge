---
id: svm-sem-070
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-069]
---

# svm-sem-070 L3/E∞ knife 65 — Loader account-8 → account-9 skip chain

## 目标

在 account-8 executable/rent 齐备之后，覆盖 Emit 从 account-8 header 游标链式
`emitSkipAccount` 到 account-9 dup marker。同一 nonuple skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account8SkipNextInputMem` / `walkAccount8SkipNextAfterSkipChain?` /
   `evalWalkAccount8SkipNextAfterSkipChainToStack?` / `evalAbsAccount9Marker?`
2. Theorems：`walkAccount8SkipNextAfterSkipChain_verified`、
   `evalWalkAccount8_skip_next_marker_0xff`、
   `walkAccount8SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 65 section
- Spec guards for marker=0xff / 0xB5 vs abs loads

## 仍未覆盖

account-9 meta/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
