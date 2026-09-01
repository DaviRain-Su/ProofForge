---
id: svm-sem-002
track: E-l3
status: todo
plan: ../svm-work-plan.md
rung: E2
depends-on: [svm-sem-001]
---

# svm-sem-002 L3/E2 — assembler-semantics golden 差分门

## 背景

`sbpfSemantics`（assembler-semantics）已提供 `.s → L2` 解析与步进。本片把它收成
对 ProofForge emit 的可重复差分门。

## 目标

1. 选定 corpus（至少 Counter + 1 容器例）  
2. emit `.s` → parse → step 与期望观察差分  
3. CI 可跑子集；失败定位到具体 program  

## 交付

- golden / 脚本 / CI 接线说明  
- 与 `SemanticsBridge.lean` 的入口文档  

## 非目标

证明每个 golden 的 kernel correspondence（那是 E3+）；本片先稳住工程差分门。
