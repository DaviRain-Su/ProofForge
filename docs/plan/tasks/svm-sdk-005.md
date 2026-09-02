---
id: svm-sdk-005
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F2
depends-on: [svm-rt-002]
---

# svm-sdk-005 Token-2022 extension Sdk facade

## 目标

把 svm-rt-002 的 extension 语义收成 `Svm.Sdk` 可组合 facade；应用不直连 Runtime leaf。

## 交付

1. typed view + effect wrappers — **done**
   - `ProofForge.Svm.Sdk.Token2022`：`transferCheckedMintClose`、`MintCloseAuthority`、`parseMintCloseAuthority`、`viewOf`
2. classic Token 路径不受影响 — **done**（`Sdk.Token` / base `Examples.Token2022` 不变）
3. 未知 extension 仍拒绝 — **done**（host parse 走 `evaluatePolicy mintClosePolicy`）

## 验收证据

- Lean `#guard`s in `Tests.Token2022MintCloseSpec`（classic accept/none、mint-close parse、fee reject）
- Mollusk dual consumers covered under svm-rt-002

## 非目标

Emit 里出现 extension 专用 recipe 名。
