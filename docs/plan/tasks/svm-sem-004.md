---
id: svm-sem-004
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E4
depends-on: [svm-sem-003]
---

# svm-sem-004 L3/E4 — AccountWords ↔ typed storev 桥

## 目标

把 Track A 的账户字模型（`AccountWords` / field write）与 Solanalib 内存
`storev`/`loadv` 在 **有界槽** 上对齐。

## 交付

1. 选定布局（例如 Counter value slot 或 Queue count/head/slot）  
2. 定理：模型写 ≡ typed store；模型读 ≡ typed load（在合法几何下）  
3. OOB / 未对齐路径 fail closed 或显式排除  

## 为何重要

这是「SDK L2 证明」和「sBPF L3」的接缝：同一主语既有代数又有可执行语义。

## 非目标

任意地址空间；heap bump 全模型；CPI 可见性。
