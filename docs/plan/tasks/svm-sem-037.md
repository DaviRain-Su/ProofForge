---
id: svm-sem-037
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-036]
---

# svm-sem-037 L3/E∞ knife 32 — Loader account-4 signer/writable after skip chain

## 目标

在 account-4 header/key 齐备之后，覆盖 Emit 对 account-4 的 signer/writable 标志：
`ldxb` header+1 与 header+2。同一 quadruple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account4FlagsInputMem` / `walkAccount4FlagsAfterSkipChain?` /
   `evalWalkAccount4FlagsAfterSkipChainToStack?` / `evalAbsAccount4Flags?`
2. Theorems：`walkAccount4FlagsAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_signer_writable_1`、
   `walkAccount4FlagsAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 32 section
- Spec guards for signer/writable=`1/1` and abs-load case `1/0`

## 仍未覆盖

account-4 lamports/data_len/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
