---
id: svm-sem-028
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-027]
---

# svm-sem-028 L3/E∞ knife 23 — Loader account-2 → account-3 skip chain

## 目标

在 account-2 executable/rent 齐备之后，覆盖 Emit 链式 `emitSkipAccount`：从 account-0
skip 经 account-1、account-2 zero-dataLen skip 到 account-3 dup marker。证明 walked 加载与
绝对 `r6`-相对加载一致。

## 交付

1. `account2SkipNextInputMem` / `walkAccount2SkipNextAfterSkipChain?` /
   `evalWalkAccount2SkipNextAfterSkipChainToStack?` / `evalAbsAccount3Marker?`
2. Theorems：`walkAccount2SkipNextAfterSkipChain_verified`、
   `evalWalkAccount2_skip_next_marker_0xff`、
   `walkAccount2SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 23 section
- account-3 header at `account2RentEpochOffset + 8`

## 仍未覆盖

account-3 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
