---
id: svm-sem-006
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-001]
---

# svm-sem-006 L3/E∞ knife — walked `r7` instruction-data cursor

## 目标

把 EntryAdapter / raw Borsh 路径使用的 **walked `r7` instruction-data cursor**
（`ldxdw` + width advance）接进 Solanalib，作为 Agave/ELF 主机完备（E∞）的第一刀，
而不是继续把「walked r7」写进 E0–E5 的非目标清单后就停住。

## 交付

1. Typed walk fragment：`walkArgU64?` — `ldxdw r1,[r7+0]; add64 r7,8; stxdw [r10+off],r1`
2. Counter 形 arg0：walked cursor 与 E1 绝对 `.arg` materialization 在 staged stack word 上一致
3. 具体例：arg0=5 stages 5，且 `r7` 前进 8
4. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife：`walkArgU64?` / `counterWalkedArgRegs` /
  `evalWalkArgToStack?` / `evalAbsArgToStack?`
- Theorems: `walkArgU64_verified`, `evalWalkArg_arg0_5`, `walkArg_eq_absArg_stack`
- Docs: `docs/modules/solanalib.md` E∞ knife note

## 仍未覆盖（诚实非声称）

Loader-v3 account/instruction serialization；syscall/CPI/sysvar 主机；ELF accept；
多字段 cursor 流水线；与 Agave 字节级 ELF 一致。
