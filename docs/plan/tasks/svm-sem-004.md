---
id: svm-sem-004
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E4
depends-on: [svm-sem-003]
---

# svm-sem-004 L3/E4 — AccountWords ↔ typed storev 桥

## 目标

把 Track A 的账户字模型（`AccountWords` / field write）与 Solanalib 内存
`storev`/`loadv` 在 **有界槽** 上对齐。

## 交付

1. 选定布局（Counter value slot = account-data word 1） — **done**
2. 定理：模型写 ≡ typed store；模型读 ≡ typed load（在合法几何下） — **done**
3. OOB / 未对齐路径 fail closed 或显式排除 — **done**

## Evidence

- `ProofForge/Svm/Solanalib.lean` E4：`accountWordByteOffset` / `storeAccountWord?` /
  `loadAccountWord?` / `projectFieldWrite?` / `counterValueFieldWord?` on Counter `value` word
- Geometry: `counterValueWord_offset` (`ACC0_DATA + 8` = 104)
- Track A: `mFieldWord_counterValue`; `projectFieldWrite_eq_storeAccountWord`;
  `mReadField_matches_loadAccountWord`
- Emitter seam: `storeAccountWord_eq_evalStaticStore`
- Fail-closed: `loadAccountWord_unmapped`, `storeAccountWord_oob_static`,
  `projectFieldWrite_oob_index`
- `Tests/SolanalibSpec.lean` E4 `#guard`s
- Theorems use `native_decide`

## 依赖

E3 Counter CFG correspondence；Track A `StorageModel` field algebra.

## 非目标

任意地址空间；heap bump 全模型；CPI 可见性；Queue 全函数 L3（E5）。
