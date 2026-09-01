---
id: svm-sem-021
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-020]
---

# svm-sem-021 L3/E∞ knife 16 — Loader account-1 → account-2 skip chain

## 目标

在 account-1 executable/rent 齐备之后，覆盖 Emit 链式 `emitSkipAccount`：从 account-0
skip 到 account-1 header，再从 account-1 zero-dataLen skip 到 account-2 dup marker。
证明 walked 加载与绝对 `r6`-相对加载一致。

## 交付

1. `account1SkipNextInputMem` / `walkAccount1SkipNextAfterAccount0Skip?` /
   `evalWalkAccount1SkipNextAfterAccount0SkipToStack?` / `evalAbsAccount2Marker?`
2. Theorems：`walkAccount1SkipNextAfterAccount0Skip_verified`、
   `evalWalkAccount1_skip_next_marker_0xff`、
   `walkAccount1SkipNextAfterAccount0Skip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 16 section
- account-2 header at `account1RentEpochOffset + 8`

## 仍未覆盖

account-2 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
