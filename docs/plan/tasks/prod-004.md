# prod-004 — P3：Release 打包（CLI + SDK）

## 目标

按 git tag 发布可安装制品：CLI 二进制 + 可 `require` 的 SDK，并钉死工具链与能力清单。

## 范围

- GitHub Release workflow：构建并上传 `pf`（linux/mac）、checksums、changelog
- 同 tag `vX.Y.Z` 作为 Lake `require … @ "vX.Y.Z"` 的 SDK 源
- `pf --version` 打印 CLI、Lean、sbpf/solc/wat2wasm 等 pin
- Release notes 附带本版本 fail-closed capability 摘要（摘自 capability matrix）

## 不改

- 不强制拆独立 git 仓；不引入第二套包注册中心。

## 验收

1. 从干净机器：安装 Release 中的 `pf`，`require` 对应 tag 的 SDK，用模板工程 `pf build` 成功。
2. 版本号与 pin 在 CLI 与 Release notes 一致。
3. SDK 包 root 不含 Examples/Tests。

## 依赖

prod-003。
