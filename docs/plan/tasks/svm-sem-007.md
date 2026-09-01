---
id: svm-sem-007
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-006]
---

# svm-sem-007 L3/E∞ knife 2 — two consecutive walked `r7` args

## 目标

在 `svm-sem-006` 单字段 walked cursor 之上，覆盖 EntryAdapter Borsh 多字段流水线：同一
`r7` 连续 walk 两个 u64，并与 E1 绝对 `.arg` materialization 在两个 staged stack word 上一致。

## 交付

1. `counterInputMem2` / `evalWalkTwoArgsToStack?` / `evalAbsArg1ToStack?`
2. 具体例：arg0=5、arg1=9；`r7` 前进 16
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean`：`walkTwoArgs_eq_absArgs_stack` /
  `evalWalkTwoArgs_arg0_5_arg1_9`
- Spec guards for the two-arg pipeline

## 仍未覆盖

Loader-v3 account/instruction serialization；syscall/CPI/sysvar；ELF accept；
变长 Borsh / option / string cursor；与 Agave 字节级 ELF 一致。
