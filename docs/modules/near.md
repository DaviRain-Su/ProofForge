# ProofForge.Wasm.Near

## Purpose

WASM 家族的第二条链：**NEAR Protocol**。经 `Core.Target.Registration` 注册。
产物是 **`.wasm`**：Lean 直接 lowering 到 WAT，import 表钉 NEAR runtime 的
`env`（`input` / `register_len` / `read_register` / `storage_read` /
`storage_write` / `value_return` / `panic_utf8`），组装器是锁定的
`wat2wasm 1.0.41`。外来叶子经 [`Wasm.Family`](wasm.md) fail closed。

基础标量绑定历史仓 proof_forge 的 profile `near-wasm-raw-u64-v1`：这**不是** JSON
ABI，也**不是** XRPL 的 C 参数 `i32`/`i64` export。标量 method 的 `env.input`
恰好为 `8 * paramCount` bytes little-endian。wsm-near-bytes-001 另为单个 `BoundedBytes` /
`BoundedString` 参数绑定 canonical Borsh `u32_le(length) || active bytes`（capacity 1..64；
String strict UTF-8）。wsm-near-output-001 使用 guest arena 为 bounded bytes/String 及单
limb unsigned array view 输出同样的 canonical active prefix；scalar view 仍恰好返回
8-byte little-endian。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Near.Ops` | NEAR context 值叶、static log effect 与方言检查 | 其它链的方言、collection recipe |
| `Near.Host` | import 模块 `env`、digest 域 `near-raw-u64\|`、header | XRPL `host_lib`、Data blob sfield |
| `Near.Codec` | bounded bytes/String 输入与 bounded view 输出的 canonical Borsh 计划/资源上限 | collection layout、JSON、mutating bounded output |
| `Near.Memory` | invocation-local checked arena model、8-byte alignment、`memory.grow`/OOM 边界 | durable state、source-visible pointer、通用 malloc/free ABI |
| `Near.Sdk.Transient` | compiler-erased `Buffer64` capacity 与 begin/set/get/finish 表面 | persistent Vector/Map/Queue、任意 raw pointer |
| `Near.IR` | registration、方言标签、target-owned bounded input/output frame binding | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Near.Emit` | `env` import、KV 8-byte LE 存储、Borsh input/output、strict UTF-8、checked arena lowering | XRPL Data-blob 发射器、Vector/Map host opcode |
| `Near.Assemble` | 写 `{name}.wat`，调锁定 `wat2wasm 1.0.41` 出 `{name}.wasm` | rustc / cargo / near-sandbox |
| `Near.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Near.Commands` | `#pf_near_build` / `#pf_near_dump` | 新 DSL |

## 诚实边界

- `deployable=false`：不声称 nearcore / near-sandbox / cargo-near / testnet / 主网；
- 组装器是锁定的 `wat2wasm 1.0.41`；rustc / cargo 不是 Tool Lock；
- 家族共享 `Wasm.Emit` 目前按 XRPL Data-blob 形状注入 host；NEAR 的 env/KV
  ABI 不拟合，所以 `Near.Emit` 拥有自己的 import 表。加第三条链时不要把
  NEAR 的 `env` 塞进 `Wasm.Host.Contract`；
- 工程门分两层：`runtime-tests/near/check.sh` 断言 import 表 + wasm magic；
  `runtime-tests/near/counter.sh` 起锁定 `near-sandbox 2.13.0`、部署本仓
  `Counter.wasm`、跑 initialize / increment / overflow / get。缺 sandbox /
  python 依赖则 skip；`context.sh` 验证 context/log；`bytes.sh` 验证 exact Borsh、
  inactive zeroing 和 UTF-8 正反矩阵；`memory.sh` 验证跨 source-declared 首页的 arena
  分配/复用/清零以及 bounds、stale handle、wrong capacity、double begin traps（nearcore
  可把 initial memory 规范化得更大，实际 grow 路径由 model + WAT gate 钉住）。不是
  「artifact 已被证明」；`output.sh` 验证 exact bytes/String/UInt16-array Borsh、input/output
  round-trip、capacity 和 output UTF-8 failures。

CLI：`pf build --target near`。当前注册 `Counter`、`NearCtx`、`NearBytes`、`NearMemory`、
`NearOutput`。
