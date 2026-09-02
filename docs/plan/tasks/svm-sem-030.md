---
id: svm-sem-030
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-029]
---

# svm-sem-030 L3/E∞ knife 25 — Loader account-3 signer/writable after skip chain

## 目标

在 account-3 header/key 齐备之后，覆盖 Emit 对 account-3 的 signer/writable gate：
`ldxb` header+1 与 header+2。同一 triple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account3FlagsInputMem` / `walkAccount3FlagsAfterSkipChain?` /
   `evalWalkAccount3FlagsAfterSkipChainToStack?` / `evalAbsAccount3Flags?`
2. Theorems：`walkAccount3FlagsAfterSkipChain_verified`、
   `evalWalkAccount3_after_skip_signer_writable_1`、
   `walkAccount3FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 25 section
- Spec guards for signer/writable=`1`/`1` and `1`/`0` vs abs loads

## 仍未覆盖

account-3 lamports/data_len/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
