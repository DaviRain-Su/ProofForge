# prod-001 — P0：SDK 导入表面冻结

## 目标

在拆 Lake 包之前，先把「合约该 import 什么」写成可执行合同，并用 CI 挡住回归。

## 范围

- 文档：用户/Examples 推荐 `ProofForge.Svm.Sdk` / `ProofForge.Evm.Sdk`（+ `ProofForge.Attr`）；禁止推荐伞模块 `import ProofForge`。
- CI：扩展 `scripts/check_ownership.py`（或并列脚本）
  - Examples **新增**文件不得 `import ProofForge` 伞模块（可允许存量白名单，但不得再增加）。
  - `ProofForge/{Svm,Evm}/Sdk/**` 不得 import 同 target 的 `Emit` / `Assemble` / `Registry`。
- README / 快速开始：合约示例改为 SDK import。

## 不改

- `lakefile.lean` 包图、IR/Emit 语义、Registry digest。

## 验收

1. 守卫脚本在 CI 红灯于故意引入的伞 import / Sdk→Emit import。
2. 文档与 [productization.md](../productization.md) §3.2 一致。
3. 全量既有回归仍绿。

## 实现清单（本 PR）

1. 改 README / 快速开始示例 import。
2. 扩展 ownership 守卫：Examples 新增伞 import、Sdk→Emit/Assemble/Registry。
3. 存量伞 import 白名单（只减不增）；可选开启分批迁移但不阻塞本卡验收。
4. CI 跑守卫；加负例证明会失败。

## 依赖

无。解锁 prod-002。本卡与后续 prod-* **同一 PR #11** 交付。
