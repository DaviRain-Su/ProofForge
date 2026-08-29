# ProofForge.Wasm.Xrpl

## Purpose

WASM 家族的第一条链：**XRPL Bedrock（XLS-0101）**。经
`Core.Target.Registration` 注册。产物是 **`.wasm`**：Lean 直接 lowering 到
WAT，import 表钉 XLS-0102 的 `host_lib`（读 `home_le_field`、写 `set_data`），
组装器是锁定的 `wat2wasm 1.0.41`。外来叶子经 [`Wasm.Family`](wasm.md)
fail closed。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Xrpl.Ops` | XRPL 方言 `ValKind` / `OpExt`（v0 无宿主叶子；`reserved` 仅保 inhabitance） | 其它链的方言 |
| `Xrpl.Host` | import 模块 `host_lib`、`home_le_field` / `set_data`、sfield Data=`458779`、digest 域 `xrpl-bedrock\|` | Core→WAT 发射、v0 子集检查 |
| `Xrpl.IR` | registration 实例化、方言类型别名、ext canonical 标签 | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Xrpl.Emit` | 薄封装：把 `Xrpl.Host.contract` 注入 `Wasm.Emit` | 发射逻辑本身 |
| `Xrpl.Assemble` | 写 `{name}.wat`，调锁定 `wat2wasm 1.0.41` 出 `{name}.wasm` | rustc / cargo / bedrock / AlphaNet |
| `Xrpl.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Xrpl.Commands` | `#pf_xrpl_build` / `#pf_xrpl_dump` | 新 DSL |

## v0 子集（全部 fail closed）

- 状态：全部 UInt64 槽（width 8），按声明顺序小端打包进 home 对象 `Data` blob；
- 参数：scalar UInt64；view 结果：恰好一个 UInt64，export `-> i64`；
  mutating entry 只返回 `i32` 状态码（源声明的 public 返回值被省略，读 view）；
- ops：checked 五则、`ite`、`okState` / `returnState` / `returnU64`、
  `errorOverflow`、`storeField`；loop / local / vector / map / `errorNamed` /
  位运算 / 移位 / 未检查 `/ %` 全部拒绝；
- 无宿主 capability：ledger time / caller / hashing 不在方言里。

## 诚实边界

- 主网 `deployable=false`：XRPL 主网没有 `ContractCreate`；Hooks / EVM
  sidechain 不属于本 target；
- 组装器是锁定的 `wat2wasm 1.0.41`，对标 `solc 0.8.34` / `sbpf 0.2.2`；
  rustc / cargo / flint 不是 Tool Lock；
- XLS-0102 目前只钉 Smart Escrow host；同名函数将可从 smart contracts 访问。
  v0 只用 `host_lib.{home_le_field,set_data}`；
- 工程门分两层：`runtime-tests/xrpl/check.sh` 断言产物形状（import 表 + wasm
  magic）。本地链部署是 [wsm-003](../plan/tasks/wsm-003.md)。缺 Docker /
  bedrock 则 skip。不是「artifact 已被证明」。

## 摘要

```text
frontend Core.IR.Program（已过 Profile）
        │  Xrpl.IR.extractRegistration（经 Wasm.Family 拒绝 svm/evm 叶）
        ▼
Xrpl.IR.Program（v0 子集 fail-closed；digest 域 xrpl-bedrock|）
        ▼
WAT {name}.wat
        ▼  locked wat2wasm 1.0.41
{name}.wasm
        ▼  runtime-tests/xrpl/check.sh（import 表工程门）
```

CLI：`pf build --target xrpl`（别名 `xrpl-bedrock` / `bedrock`；`wasm` 本身会被
拒绝并提示它是家族不是链）。注册程序见 `Xrpl.Registry`；当前为 `Counter`
（digest `e029f72296e320be`）。

## 与调研文档 WAT 设想的关系

`research/06-wasm-feasibility.md` 的链上腿最初设想「通用 wasmtime + `pf` import」。
那条通用宿主不存在：链差在 host function 和存储布局。本切片是 Lean → WAT →
locked `wat2wasm` → `.wasm`，import 表由链拥有。XRPL 钉 `host_lib`，不是 `pf.*`。
