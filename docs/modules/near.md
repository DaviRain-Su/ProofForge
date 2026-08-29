# ProofForge.Wasm.Near

## Purpose

WASM 家族的第二条链：**NEAR Protocol**。经 `Core.Target.Registration` 注册。
产物是 **`.wasm`**：Lean 直接 lowering 到 WAT，import 表钉 NEAR runtime 的
`env`（`input` / `register_len` / `read_register` / `storage_read` /
`storage_write` / `value_return` / `panic_utf8`），组装器是锁定的
`wat2wasm 1.0.41`。外来叶子经 [`Wasm.Family`](wasm.md) fail closed。

v0 绑定历史仓 proof_forge 的 profile `near-wasm-raw-u64-v1`：这**不是** JSON
ABI，也**不是** XRPL 的 C 参数 `i32`/`i64` export。每个 method 的 `env.input`
恰好为 `8 * paramCount` bytes little-endian；每个 `UInt64` `value_return`
恰好为 8-byte little-endian。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Near.Ops` | NEAR 方言 `ValKind` / `OpExt`（v0 无宿主叶子） | 其它链的方言 |
| `Near.Host` | import 模块 `env`、digest 域 `near-raw-u64\|`、header | XRPL `host_lib`、Data blob sfield |
| `Near.IR` | registration 实例化、方言类型别名、ext canonical 标签 | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Near.Emit` | `env` import 表、KV 8-byte LE 存储、raw-u64 入口 ABI | XRPL Data-blob 发射器 |
| `Near.Assemble` | 写 `{name}.wat`，调锁定 `wat2wasm 1.0.41` 出 `{name}.wasm` | rustc / cargo / near-sandbox |
| `Near.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Near.Commands` | `#pf_near_build` / `#pf_near_dump` | 新 DSL |

## 诚实边界

- `deployable=false`：不声称 nearcore / near-sandbox / cargo-near / testnet / 主网；
- 组装器是锁定的 `wat2wasm 1.0.41`；rustc / cargo 不是 Tool Lock；
- 家族共享 `Wasm.Emit` 目前按 XRPL Data-blob 形状注入 host；NEAR 的 env/KV
  ABI 不拟合，所以 `Near.Emit` 拥有自己的 import 表。加第三条链时不要把
  NEAR 的 `env` 塞进 `Wasm.Host.Contract`；
- 工程门 `runtime-tests/near/check.sh` 断言 import 表 + wasm magic。不是
  「artifact 已被证明」。

CLI：`pf build --target near`。当前注册 `Counter`。
