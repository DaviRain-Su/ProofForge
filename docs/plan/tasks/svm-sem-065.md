---
id: svm-sem-065
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-064]
---

# svm-sem-065 L3/E∞ knife 60 — Loader account-8 signer/writable after skip chain

## 目标

在 account-8 header/key 齐备之后，覆盖 Emit 对 account-8 signer/writable：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 octuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account8FlagsInputMem` / `walkAccount8FlagsAfterSkipChain?` /
   `evalWalkAccount8FlagsAfterSkipChainToStack?` / `evalAbsAccount8Flags?`
2. Theorems：`walkAccount8FlagsAfterSkipChain_verified`、
   `evalWalkAccount8_after_skip_signer_writable_1`、
   `walkAccount8FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 60 section
- Spec guards for signer=1 / writable=0 vs abs loads

## 仍未覆盖

account-8 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
