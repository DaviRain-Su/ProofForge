---
id: svm-sem-016
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-015]
---

# svm-sem-016 L3/E∞ knife 11 — Loader account-1 signer/writable after skip

## 目标

在 account-1 header/key（`0x2868`/`0x2870`）齐备之后，覆盖 Emit 对 account-1 的
signer/writable 门控：`ldxb` header+1 / +2（绝对 `0x2869` / `0x286a`）。同一 skip
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1FlagsInputMem` / `walkAccount1FlagsAfterSkip?` /
   `evalWalkAccount1FlagsAfterSkipToStack?` / `evalAbsAccount1Flags?`
2. Theorems：`walkAccount1FlagsAfterSkip_verified`、
   `evalWalkAccount1_after_skip_signer_writable_1`、
   `walkAccount1FlagsAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 11 section
- Spec guards for signer/writable=`1`/`0` vs abs loads at `0x2869`/`0x286a`

## 仍未覆盖

account-1 lamports/data_len/owner/executable/rent；完整 multi-account 向量；
syscall/CPI/sysvar；ELF accept。
