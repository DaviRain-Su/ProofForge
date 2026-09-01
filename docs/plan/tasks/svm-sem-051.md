---
id: svm-sem-051
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-050]
---

# svm-sem-051 L3/E∞ knife 46 — Loader account-6 signer/writable after skip chain

## 目标

在 account-6 header/key 齐备之后，覆盖 Emit 对 account-6 signer/writable：
`ldxb` header+1 与 header+2。同一 sextuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account6FlagsInputMem` / `walkAccount6FlagsAfterSkipChain?` /
   `evalWalkAccount6FlagsAfterSkipChainToStack?` / `evalAbsAccount6Flags?`
2. Theorems：`walkAccount6FlagsAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_signer_writable_1`、
   `walkAccount6FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 46 section
- Spec guards for signer=1 / writable=0 vs abs loads

## 仍未覆盖

account-6 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
