# ProofForge.Wasm.Xrpl

## Purpose

WASM 家族的第一条链：**XRPL Bedrock（XLS-0101）**。经
`Core.Target.Registration` 注册的 XRPL 方言，artifact 是 scaffold-xrp 方言
Rust 源（`xrpl_wasm_std` 的 `get_current_contract_call` / `get_data` /
`set_data`、`#[unsafe(no_mangle)] pub extern "C"` 导出）。不改通用
`Core.Ops` / `Core.CFG` / frontend，只加注册；外来叶子经
[`Wasm.Family`](wasm.md) 的家族级拒绝 fail closed。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Xrpl.Ops` | XRPL 方言 `ValKind` / `OpExt`（v0 无宿主叶子；`reserved` 仅保 inhabitance，`wellFormed` 拒绝） | 其它链的方言、XRPL host capability 键 |
| `Xrpl.Host` | 存储（`get_data`/`set_data`）、入口 ABI（`extern "C"` + `i32` 状态码 / `u64` view）、digest 域 `xrpl-bedrock\|`、header / prelude | 共享 Core→Rust 发射、v0 子集检查 |
| `Xrpl.IR` | registration 实例化（经 Family 拒 svm/evm 叶）、方言类型别名、ext canonical 标签 | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Xrpl.Emit` | 薄封装：把 `Xrpl.Host.contract` 注入 `Wasm.Emit` | 发射逻辑本身 |
| `Xrpl.Assemble` | zero-tool 写 `{name}.rs`（digest 行钉 canonical 身份） | rustc / cargo / bedrock / AlphaNet |
| `Xrpl.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Xrpl.Commands` | `#pf_xrpl_build` / `#pf_xrpl_dump` | 新 DSL |

## v0 子集（全部 fail closed）

- 状态：全部 UInt64 槽（width 8），经合约 pseudo-account 的
  `read_u64` / `write_u64` 读写；
- 参数：scalar UInt64；view 结果：恰好一个 UInt64，`-> u64` FFI-safe 导出；
  mutating entry 只返回 `i32` 状态码（源声明的 public 返回值被省略，读 view）；
- ops：checked 五则、`ite`、`okState` / `returnState` / `returnU64`、
  `errorOverflow`、`storeField`；loop / local / vector / map / `errorNamed` /
  位运算 / 移位 / 未检查 `/ %` 全部拒绝；
- 无宿主 capability：ledger time / caller account / hashing 不在方言里，直到
  其 XRPL wasm 级 import ABI 被钉死（旧仓 proof_forge 的 ADR-0052 已冻 Rust 侧
  符号，但 wasm 级 ABI 未钉）。

## 诚实边界（来自 proof_forge XRPL 研究的事实）

- artifact 是 **source-only、zero-tool**：`deployable=false`；不声称 bedrock /
  rippled / `ContractCreate` / `ContractCall` / AlphaNet / 主网；
- 真实编译面是 ambient `cargo build --target wasm32-unknown-unknown --release`
  + `xrpl-wasm-std`（git rev `ffbe88da26df27e59a72b6202883f42f696933cc`，来自
  scaffold-xrp）；rustc/cargo 不是 Tool Lock 成员；
- XRPL 主网没有 `ContractCreate`；Hooks / EVM sidechain 不属于本 target；
- 本仓工程门是 `runtime-tests/xrpl/check.sh`：生成源对**本地 stub crate**
  cargo check。stub 不是真 crate，该门只验证生成源的类型正确性，不是
  「artifact 已被证明」或「可在 XRPL 部署」的声称。

## 摘要

```text
frontend Core.IR.Program（已过 Profile）
        │  Xrpl.IR.extractRegistration（经 Wasm.Family 拒绝 svm/evm 叶）
        ▼
Xrpl.IR.Program（v0 子集 fail-closed；digest 域 xrpl-bedrock|）
        ▼
Bedrock 方言 Rust 源 {name}.rs（zero-tool）
        ▼  runtime-tests/xrpl/check.sh（stub crate cargo check，工程门）
```

CLI：`pf build --target xrpl`（别名 `xrpl-bedrock` / `bedrock`；`wasm` 本身会被
拒绝并提示它是家族不是链）。注册程序见 `Xrpl.Registry`；当前为 `Counter`
（四场景：initialize / increment ok / increment overflow / get，加 decrement /
divide / modulo / scale / nonzero 同子集）。

## 与调研文档 WAT 设想的关系

`research/06-wasm-feasibility.md` 的链上腿最初设想「通用 wasmtime + `pf` import
合同 → WAT → wat2wasm，选链推迟」。本切片把第一条链定为 XRPL：XRPL Bedrock 的
真实编译面是 Rust + ambient cargo + `xrpl_wasm_std`，且其 wasm 级 host import
ABI 从未被钉死（旧仓只钉了 Rust crate rev）。因此 v0 的 artifact 改为该方言的
Rust 源——与 EVM 发 Yul 给 locked solc 同构（源语言交给链生态自己的编译面），
而不是发明一套未经验证的 WAT import 表。通用 `pf` import / wasmtime fuel /
wat2wasm 路线仍是其它链的选项，但需先钉各自宿主的真实 ABI。