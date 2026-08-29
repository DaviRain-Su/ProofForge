# ProofForge.Wasm.Xrpl

## Purpose

WASM 家族的第一条链：**XRPL Bedrock（XLS-0101）**。经
`Core.Target.Registration` 注册。产物是 **`.wasm`**：Lean 直接 lowering 到
WAT，import 表钉本 Bedrock 镜像的 `host_lib`（读
`get_current_ledger_obj_field`、写 `set_data_object_field`、参数
`function_param`），组装器是锁定的 `wat2wasm 1.0.41`。外来叶子经
[`Wasm.Family`](wasm.md) fail closed。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Xrpl.Ops` | XRPL 方言 `ValKind` / `OpExt`（v0 无宿主叶子；`reserved` 仅保 inhabitance） | 其它链的方言 |
| `Xrpl.Host` | import 模块 `host_lib`、`get_current_ledger_obj_field` / `get/set_data_object_field` / `function_param`、digest 域 `xrpl-bedrock\|` | Core→WAT 发射、v0 子集检查 |
| `Xrpl.IR` | registration 实例化、方言类型别名、ext canonical 标签 | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Xrpl.Emit` | 薄封装：把 `Xrpl.Host.contract` 注入 `Wasm.Emit` | 发射逻辑本身 |
| `Xrpl.Assemble` | 写 `{name}.wat`，调锁定 `wat2wasm 1.0.41` 出 `{name}.wasm` | rustc / cargo / bedrock / AlphaNet |
| `Xrpl.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Xrpl.Commands` | `#pf_xrpl_build` / `#pf_xrpl_dump` | 新 DSL |
| `Xrpl.Sdk` | `@[pf_inline]`：`Context`、`AccountId.eq`、`Access.requireOwner`、`Hash.sha512HalfLit` | 新 host / Vec / Map / EVM hashed storage |

## v0 子集（全部 fail closed）

- 状态：全部 UInt64 槽（width 8），每个槽一个 `ContractData.ContractJson` 字段
  （STI_UINT64 + 大端 8 字节）；挂在 Contract SLE 的 `sfOwner` 下，因为合约
  AccountRoot 余额为 0、不够 reserve。本镜像的 `update_data` 不落账本；
- 参数：scalar UInt64，经 `function_param` 拷进 linear memory；export 无 wasm
  参数。view 结果：恰好一个 UInt64，export `-> i64`（本宿主不填
  `meta.ReturnValue`，工程门从 `ContractJson` 读状态）；
  mutating entry 只返回 `i32` 状态码（源声明的 public 返回值被省略，读 view）；
- ops：checked 五则、`ite`、`okState` / `returnState` / `returnU64`、
  `errorOverflow`、钉死的 `errorNamed "unauthorized"`（wasm `i32` 状态码 3）、
  `storeField`；loop / local / vector / map / 其它 named error /
  位运算 / 移位 / 未检查 `/ %` 全部拒绝；
- 宿主 capability（wsm-005）：`Xrpl.Runtime.xrplCaller20` / `xrplSelf20` /
  `xrplLedgerSqn` / `xrplParentTime`。hash：`xrplSha512HalfLit` →
  `host_lib.compute_sha512_half`，只返回首个小端 UInt64。完整 32B / 动态输入 /
  keccak 仍 fail closed。

## 诚实边界

- 主网 `deployable=false`：XRPL 主网没有 `ContractCreate`；Hooks / EVM
  sidechain 不属于本 target；
- 组装器是锁定的 `wat2wasm 1.0.41`，对标 `solc 0.8.34` / `sbpf 0.2.2`；
  rustc / cargo / flint 不是 Tool Lock；
- XLS-0102 目前只钉 Smart Escrow host；同名函数将可从 smart contracts 访问。
  v0 用 `host_lib.{get_current_ledger_obj_field,get_data_object_field,set_data_object_field,function_param}`；
- 工程门分两层：`runtime-tests/xrpl/check.sh` 断言产物形状（import 表 + wasm
  magic）；`runtime-tests/xrpl/counter.sh` 起 Bedrock 本地节点、部署本仓
  `Counter.wasm`（`--skip-build`）、跑 initialize / increment / overflow / get。
  `ctx.sh` 验环境叶；`own.sh` 验三叶比较（非 owner 状态码 3）；
  `hash.sh` 验 `compute_sha512_half("vault")` 首个小端 u64；
  `rt2.sh` 验 parent hash 低 8 字节和 base fee；
  `vec.sh` 验编译期命名槽 `xs_0`…`xs_2`（越界 overflow）。
  缺 Docker / bedrock 则 skip。不是「artifact 已被证明」。

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
拒绝并提示它是家族不是链）。活公开网用 `--target xrpl-alphanet`（别名
`alphanet`）：同一 IR，host 名换成 XLS-0102（`home_le_field` / `tx_field` /
`ldgr_index` / `sha512_half`），view 返回 `i32`，存储所有者走
`tx_field(sfAccount)`。部署/调用是本仓
`runtime-tests/xrpl/{alphanet-rpc.js,smoke.sh}`，不是 `bedrock deploy`。
现成 Bedrock Docker **不能**当 AlphaNet 本地模拟（host 表不同）。
注册程序见 `Xrpl.Registry`；当前为 `Counter`
（digest `e029f72296e320be`）、`XrplCtx`、`XrplOwn`、`XrplHash`、`XrplRt2`、
`XrplVec`（digest `e47db263444f8c7e`，编译期 JSON 槽 `xs_0`…`xs_2`）。

## 与调研文档 WAT 设想的关系

`research/06-wasm-feasibility.md` 的链上腿最初设想「通用 wasmtime + `pf` import」。
那条通用宿主不存在：链差在 host function 和存储布局。本切片是 Lean → WAT →
locked `wat2wasm` → `.wasm`，import 表由链拥有。XRPL 钉 `host_lib`，不是 `pf.*`。
