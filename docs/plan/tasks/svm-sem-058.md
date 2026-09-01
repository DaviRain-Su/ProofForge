---
id: svm-sem-058
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-057]
---

# svm-sem-058 L3/E∞ knife 53 — Loader account-7 signer/writable after skip chain

## 目标

在 account-7 header/key 齐备之后，覆盖 Emit 对 account-7 signer/writable：
`ldxb` header+1 与 header+2。同一 septuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account7FlagsInputMem` / `walkAccount7FlagsAfterSkipChain?` /
   `evalWalkAccount7FlagsAfterSkipChainToStack?` / `evalAbsAccount7Flags?`
2. Theorems：`walkAccount7FlagsAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_signer_writable_1`、
   `walkAccount7FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 53 section
- Spec guards for signer=1 / writable=0 vs abs loads

## 仍未覆盖

account-7 budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
