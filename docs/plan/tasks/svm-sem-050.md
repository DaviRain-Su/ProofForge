---
id: svm-sem-050
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-049]
---

# svm-sem-050 L3/E∞ knife 45 — Loader account-6 header/key after skip chain

## 目标

在 account-6 skip chain 齐备之后，覆盖 Emit 对 account-6 header/key：
`ldxb` marker 与 `ldxdw` header+8 key。同一 sextuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account6MetaInputMem` / `walkAccount6MetaAfterSkipChain?` /
   `evalWalkAccount6MetaAfterSkipChainToStack?` / `evalAbsAccount6Meta?`
2. Theorems：`walkAccount6MetaAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_key_0x76`、
   `walkAccount6MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 45 section
- Spec guards for key=0x76 / marker=0xB1 vs abs loads

## 仍未覆盖

account-6 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
