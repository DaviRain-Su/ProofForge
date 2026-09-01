# prod-002 — P1：Lake 包拆分（Sdk vs Compiler）

## 目标

让 SVM/EVM SDK 成为可单独依赖的 `lean_lib`，其传递闭包不含 Emit/Assemble/Registry。

## 范围

- `lakefile.lean` 增加至少：
  - `ProofForgeSvmSdk`
  - `ProofForgeEvmSdk`
  - `ProofForgeCompiler`（含 Extract、各 target Emit/Assemble、Cli）
  - 按需拆出 `ProofForgeAttr` / `ProofForgeCore`
- 伞模块 `ProofForge.lean` 仅供 compiler workspace / 仓内便利；用户模板不引用。
- CLI：去掉写死的 `Examples.<Name>`；改为 `--module` / `pf.toml` 配置（最小可用即可）。
- CI：断言 `import ProofForge.Svm.Sdk` / `Evm.Sdk` 的 import graph 不含 Emit。

## 不改

- 链上字节、IR digest、Runtime 语义（文件搬家必须 byte-identical 产物）。

## 验收

1. 隔离 Lake 包（或 `lake env` 打印）只链 SDK lib 时可 elaborator 合约文件。
2. `pf build --target svm --module <非 Examples 模块>` 在夹具工程上可跑通（可用临时 fixture）。
3. 本仓 Examples/Tests 全绿。

## 依赖

prod-001。解锁 prod-003。
