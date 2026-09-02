---
id: svm-sem-064
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-063]
---

# svm-sem-064 L3/E∞ knife 59 — Loader account-8 header/key after skip chain

## 目标

在 account-8 dup marker 齐备之后，覆盖 Emit 对 account-8 header/key：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 octuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account8MetaInputMem` / `walkAccount8MetaAfterSkipChain?` /
   `evalWalkAccount8MetaAfterSkipChainToStack?` / `evalAbsAccount8Meta?`
2. Theorems：`walkAccount8MetaAfterSkipChain_verified`、
   `evalWalkAccount8_after_skip_key_0x78`、
   `walkAccount8MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 59 section
- Spec guards for key=0x78 / marker=0xB4 vs abs loads

## 仍未覆盖

account-8 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
