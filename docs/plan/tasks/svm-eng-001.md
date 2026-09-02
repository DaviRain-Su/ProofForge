---
id: svm-eng-001
track: F-eng
status: done
plan: ../svm-work-plan.md
---

# svm-eng-001 形式化门进 CI

## 目标

把 `scripts/check_no_sorry.py` 与形式化相关 lake 目标稳定钉进 Lean/SVM lane。

## 交付

1. **Lean lane**（`.github/workflows/ci.yml`）：保留 ownership / artifact / no-sorry；新增具名
   `lake build Tests.ProofSpec Tests.SolanalibSpec Tests.SemanticsSpec`，再跑全量 `Tests`
2. **SVM lane**：在 Examples/program build 前跑 `check_ownership.py` + `check_no_sorry.py`
3. **本地说明**：`README.md`「本地形式化门」复制命令；失败行格式 `path:line: …`

## 非目标

新建独立 lake package；`svm-sem-002` corpus 差分门（另片）。

## 证据

- CI: `.github/workflows/ci.yml` Lean formalization step + SVM ownership/no-sorry
- Docs: `README.md` 本地门禁段；本任务 done
