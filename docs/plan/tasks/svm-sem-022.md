---
id: svm-sem-022
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-021]
---

# svm-sem-022 L3/E∞ knife 17 — Loader account-2 header/key after skip chain

## 目标

在 account-1→account-2 skip chain 齐备之后，覆盖 Emit 对 account-2 的 header/key
加载：`ldxb` marker / `ldxdw` key at `+8`。证明 walked 加载与绝对 `r6`-相对加载一致。

## 交付

1. `account2MetaInputMem` / `walkAccount2MetaAfterSkipChain?` /
   `evalWalkAccount2MetaAfterSkipChainToStack?` / `evalAbsAccount2Meta?`
2. Theorems：`walkAccount2MetaAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_key_0x72`、
   `walkAccount2MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 17 section
- account-2 key at `account2HeaderOffset + 8`

## 仍未覆盖

account-2 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
