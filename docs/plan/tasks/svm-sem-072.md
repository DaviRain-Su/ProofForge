---
id: svm-sem-072
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-071]
---

# svm-sem-072 L3/E∞ knife 67 — Loader account-9 signer/writable after skip chain

## 目标

在 account-9 header/key 齐备之后，覆盖 Emit 对 account-9 signer/writable：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9FlagsInputMem` / `walkAccount9FlagsAfterSkipChain?` /
   `evalWalkAccount9FlagsAfterSkipChainToStack?` / `evalAbsAccount9Flags?`
2. Theorems：`walkAccount9FlagsAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_signer_writable_1`、
   `walkAccount9FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 67 section
- Spec guards for signer=1 / writable=0 vs abs loads

## 仍未覆盖

account-9 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
