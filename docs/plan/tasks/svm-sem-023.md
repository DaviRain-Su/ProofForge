---
id: svm-sem-023
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-022]
---

# svm-sem-023 L3/E∞ knife 18 — Loader account-2 signer/writable after skip chain

## 目标

在 account-2 header/key 齐备之后，覆盖 Emit 对 account-2 的 signer/writable 门控：
`ldxb` header+1 / +2。同一 skip chain 推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account2FlagsInputMem` / `walkAccount2FlagsAfterSkipChain?` /
   `evalWalkAccount2FlagsAfterSkipChainToStack?` / `evalAbsAccount2Flags?`
2. Theorems：`walkAccount2FlagsAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_signer_writable_1`、
   `walkAccount2FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 18 section

## 仍未覆盖

account-2 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
