---
id: svm-sem-002
track: E-l3
status: done
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

1. `Tests/SemanticsSpec.lean` — Counter + Window step goldens；named Golden parse sweep
2. `docs/modules/semantics-bridge.md` — SemanticsBridge 入口
3. `scripts/svm_semantics_golden.sh` — CI/local one-liner（`lake build Tests.SemanticsSpec`）

## Evidence

- Counter: parse band + `initialize→increment→get` + unknown-disc fail-closed
- Window: parse band + `initialize→setTail→getHead` (head unchanged)
- `firstGoldenParseFailure` carries the program name on emit→parse failures
- Lean lane already builds `Tests.SemanticsSpec` (`svm-eng-001`)

## 非目标

证明每个 golden 的 kernel correspondence（E3+）；本片只稳住工程差分门。
