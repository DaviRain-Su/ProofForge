# prod-003 — P2：`pf init` + SVM/EVM 模板

## 目标

用户不需要克隆 monorepo 即可开写：一条命令生成已接入 SDK 的工程。

## 范围

- CLI 子命令：`pf init <name> --target svm|evm`
- 模板目录（以仓内 `templates/` 为源）：
  - `templates/svm-counter`
  - `templates/evm-counter`
- 生成物含：`lakefile.lean`、`lean-toolchain`、`pf.toml`、最小合约、`README.md`
- 模板只 `require` 对应 `*Sdk`（path 指向本仓或 git tag）
- 文档：用模板走通 `pf init` → 写合约 → `pf build`

## 不改

- 新 target 语义；不把 Phoenix/协议政策写进模板。

## 验收

1. 在临时目录 `pf init demo --target svm` 后，仅依赖 SDK 即可 `pf build` 出制品。
2. EVM 同上。
3. 生成工程的 import 守卫为零违规。

## 实现清单（本 PR）

1. `pf init <name> --target svm|evm`。
2. 固化 `templates/svm-counter` / `evm-counter` 为可复制源。
3. 生成工程只依赖对应 Sdk；含 `pf.toml` + 最小 `@[pf_entry]`。
4. 隔离目录验收：`pf init` → `pf build` 出制品。
5. 文档走通 Foundry/Anchor 式上手路径。

## 依赖

prod-002。解锁 prod-004。同一 PR #11。

## 本 PR 落地状态

- [x] `pf init <name> --target svm|evm`
- [x] templates 可 `lake build`；只 import Attr + Sdk
- [x] `pf.toml` `[[program]]` 驱动 build
- [ ] 完整 assemble 制品依赖本机 `sbpf`/`solc`
