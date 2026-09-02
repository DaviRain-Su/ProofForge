---
id: svm-sem-036
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-035]
---

# svm-sem-036 L3/E∞ knife 31 — Loader account-4 header/key after skip chain

## 目标

在 account-4 dup marker skip 齐备之后，覆盖 Emit 对 account-4 的 header/key：
`ldxb` marker 与 `ldxdw` header+8。同一 quadruple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account4MetaInputMem` / `walkAccount4MetaAfterSkipChain?` /
   `evalWalkAccount4MetaAfterSkipChainToStack?` / `evalAbsAccount4Meta?`
2. Theorems：`walkAccount4MetaAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_key_0x74`、
   `walkAccount4MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 31 section
- Spec guards for marker=`0xAD`/`0xff` and key=`0x74` vs abs loads

## 仍未覆盖

account-4 signer/writable/lamports/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
