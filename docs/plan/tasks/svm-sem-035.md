---
id: svm-sem-035
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-034]
---

# svm-sem-035 L3/E∞ knife 30 — Loader account-3 → account-4 skip chain

## 目标

在 account-3 executable/rent 齐备之后，覆盖 Emit 链式 `emitSkipAccount`：从 account-0
skip 经 account-1/2/3 zero-dataLen skip 到 account-4 dup marker。证明 walked 加载与
绝对 `r6`-相对加载一致。

## 交付

1. `account3SkipNextInputMem` / `walkAccount3SkipNextAfterSkipChain?` /
   `evalWalkAccount3SkipNextAfterSkipChainToStack?` / `evalAbsAccount4Marker?`
2. Theorems：`walkAccount3SkipNextAfterSkipChain_verified`、
   `evalWalkAccount3_skip_next_marker_0xff`、
   `walkAccount3SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 30 section
- account-4 header at `account3RentEpochOffset + 8`

## 仍未覆盖

account-4 meta fields；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
