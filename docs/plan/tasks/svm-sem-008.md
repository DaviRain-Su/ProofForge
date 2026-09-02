---
id: svm-sem-008
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-007]
---

# svm-sem-008 L3/E∞ knife 3 — Loader account-0 header/key walk

## 目标

在 walked `r7` 指令数据游标之外，覆盖 Loader-v3 **account-0** 元数据游标：非 dup
标记与 pubkey 首 limb，并与绝对 `r6`-相对输入区加载一致。

## 交付

1. Offsets：`ACC0_HEADER=0x8`、`ACC0_KEY=0x10`；non-dup marker `0xff`
2. `walkAccount0Meta?`：经 `r8` 的 `ldxb` dup + `ldxdw` key，并 stage 到栈
3. Theorems：`walkAccount0Meta_verified`、`evalWalkAccount0_key_0x42`、
   `walkAccount0Meta_eq_absLoad`
4. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 3 section
- Spec guards for account-0 walk / absLoad agreement

## 仍未覆盖

完整 account 向量 walk；syscall/CPI/sysvar；ELF accept；变长 Borsh；与 Agave
字节级 ELF 一致。
