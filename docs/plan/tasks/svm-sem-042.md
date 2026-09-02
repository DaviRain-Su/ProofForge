---
id: svm-sem-042
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-041]
---

# svm-sem-042 L3/E∞ knife 37 — Loader account-4 → account-5 skip chain

## 目标

在 account-4 字段 walk 齐备之后，覆盖 Emit 从 account-4 header 游标经 zero-dataLen skip
链到 account-5 dup marker。五重 skip chain 加载的 marker 与绝对 `r6`-相对加载一致。

## 交付

1. `account4SkipNextInputMem` / `walkAccount4SkipNextAfterSkipChain?` /
   `evalWalkAccount4SkipNextAfterSkipChainToStack?` / `evalAbsAccount5Marker?`
2. Theorems：`walkAccount4SkipNextAfterSkipChain_verified`、
   `evalWalkAccount4_skip_next_marker_0xff`、
   `walkAccount4SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 37 section
- Spec guards for marker=`0xff`/`0xAE` vs abs loads

## 仍未覆盖

account-5 header/key and remaining fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
