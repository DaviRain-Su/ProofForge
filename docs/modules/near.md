# ProofForge.Wasm.Near

## Purpose

WASM 家族的第二条链：**NEAR Protocol**。经 `Core.Target.Registration` 注册。
产物是 **`.wasm`**：Lean 直接 lowering 到 WAT，import 表钉 NEAR runtime 的
`env`（`input` / `register_len` / `read_register` / `storage_read` /
`storage_write` / `storage_remove` / `storage_has_key` / `value_return` /
`panic_utf8` / `promise_batch_create` / `promise_and` / `promise_batch_then` /
`promise_batch_action_function_call` / `promise_batch_action_transfer` / `promise_return` /
`promise_results_count` / `promise_result`，按程序条件裁剪），组装器是锁定的
`wat2wasm 1.0.41`。外来叶子经
[`Wasm.Family`](wasm.md) fail closed。

基础标量绑定历史仓 proof_forge 的 profile `near-wasm-raw-u64-v1`：这**不是** JSON
ABI，也**不是** XRPL 的 C 参数 `i32`/`i64` export。标量 method 的 `env.input`
恰好为 `8 * paramCount` bytes little-endian。wsm-near-bytes-001 另为单个 `BoundedBytes` /
`BoundedString` 参数绑定 canonical Borsh `u32_le(length) || active bytes`（capacity 1..64；
String strict UTF-8）。wsm-near-output-001 使用 guest arena 为 bounded bytes/String 及单
limb unsigned array view 输出同样的 canonical active prefix；scalar view 仍恰好返回
8-byte little-endian。wsm-near-storage-001 再以同一 arena staging byte-exact bounded raw
storage key/value，并保留 nearcore 0/1 status、stale register、present-empty 和 oversized
no-copy 语义。wsm-near-vector-001 在其上加入
`DirectVector64`：四字节 compile-time prefix、`prefix || u32_le(index)` key 与 standalone
Borsh UInt64 value；它 immediate-write，逻辑 length 仍由普通 ProofForge state 持有。
wsm-near-lookup-001 再加入 default-Identity `DirectLookupMap64` / `DirectLookupSet64`：key 为
`Prefix4 || Borsh(UInt64)`，map value 为 Borsh UInt64，set value 是 exact empty bytes。
wsm-near-queue-001/wsm-near-iterable-001 在其上分别加入 bounded Queue64 与 Identity
IterableMap64/IterableSet64。wsm-near-promise-001/002 加入静态 receiver/method、bounded
arguments、lossless u128 deposit、explicit gas 的 detached/returned Promise function call；
前者不链接结果，后者在 caller state 持久化后用 `promise_return` 转发远端结果或失败。
wsm-near-promise-result/then/codec/private-001 在其上加入 bounded callback result descriptor、
静态 child → self callback、status/fits/exact-length 守卫的 Borsh UInt64 解码与显式
fallback，以及在读取 dependency result 前执行的完整 predecessor/current AccountId 鉴权。
wsm-near-promise-transfer-001 再加入静态 receiver、lossless u128 amount 的 detached/returned
native transfer；两者都用 arena staging exact 16-byte LE amount，后者在 state 持久化后链接
receipt result。wsm-near-promise-and-001 加入闭合的两个有序静态 child → `promise_and` →
self callback 图；joint Promise 只作为 callback dependency，最终只返回 callback receipt。
wsm-near-init/payable/entry-policy/uninitialized-001 再钉入口生命周期：初始化器只成功一次，
private 先于 non-payable，参数解码后 ordinary state-consuming entry 必须见到 `STATE` marker，
否则精确 panic `The contract is not initialized`。这是类似 near-sdk-rs `PanicOnDefault` 的
ProofForge fail-closed 策略；不声称 near-sdk-rs 的普通 `Default` 也必然拒绝未初始化调用。
wsm-near-state-envelope-001 把 marker 收紧为 exact 16-byte
`PFNRST01 || fnv1a64(ordered slot schema)_le`；方法逻辑升级不改变 schema identity，而字段
name/width/ABI 或顺序变化会在任何 state/result read 前精确 fail closed。它是 ProofForge
split-key 元数据，不是 near-sdk-rs 的 Borsh `STATE`。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Near.Ops` | NEAR context 值叶、static log、Promise/callback/result value/effect 与方言检查 | 其它链的方言、collection recipe |
| `Near.Host` | import 模块 `env`、digest 域 `near-raw-u64\|`、header | XRPL `host_lib`、Data blob sfield |
| `Near.Codec` | bounded bytes/String 输入与 bounded view 输出的 canonical Borsh 计划/资源上限 | collection layout、JSON、mutating bounded output |
| `Near.Memory` | invocation-local checked arena model、8-byte alignment、`memory.grow`/OOM 边界 | durable state、source-visible pointer、通用 malloc/free ABI |
| `Near.Sdk.Context/Access` | lossless context wrappers、full-AccountId equality/self-call predicate | general private/payable/init entry metadata |
| `Near.Sdk.Transient` | compiler-erased `Buffer64` capacity 与 begin/set/get/finish 表面 | persistent Vector/Map/Queue、任意 raw pointer |
| `Near.Sdk.Storage` | bounded raw key/value、单 active result、status/length/fits/indexed-byte 表面、prefix ownership | 自动 prefix/hash、persistent collection layout、raw pointer |
| `Near.Sdk.Store.Codec` | shared fixed `Prefix4`、UInt32/UInt64 suffix、Borsh UInt64/result decode | arbitrary `IntoStorageKey`、generic Borsh |
| `Near.Sdk.Store.Vector` | bounded `DirectVector64`、fixed `Prefix4`、官方 current Vector element key/value recipe | Rust `IndexMap` cache/Drop、`STATE` metadata、generic T、iterator/full `store::Vector` claim |
| `Near.Sdk.Store.Lookup` | direct Identity UInt64 map/set key/value recipe、get/has/put/remove raw status | Map cache/flush/old-value API、custom hashers、generic K/V、iteration/cardinality |
| `Near.Sdk.Promises` | static detached/returned function call/native transfer、child→self callback、两个有序 child join、bounded result descriptor、strict Borsh UInt64 fallback decode | dynamic handles、arbitrary-N/nested joins、generic Borsh |
| `Near.IR` | registration、方言标签、target-owned bounded input/output frame binding | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
| `Near.Emit` | `env` import、KV 8-byte LE + bounded raw storage、Borsh input/output、strict UTF-8、checked arena lowering | XRPL Data-blob 发射器、Vector/Map host opcode |
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
  round-trip、capacity 和 output UTF-8 failures；`storage.sh` 验证 binary/empty keys、
  insert/replace/eviction、stale-register isolation、present-empty、oversized no-copy、remove/has；
  `vector.sh` 验证 exact current element keys/Borsh values、get/set/push/pop、capacity rollback
  与大 index 在 narrowing 前被拒绝；`lookup.sh` 验证 Identity map/set exact keys、map Borsh
  values、set empty values、insert/replace/remove status、namespace split 与 key reclamation；
  `queue.sh` 验证 ProofForge bounded FIFO 的 exact slots、wraparound、full/empty rollback、逐槽
  reclamation、drained head reset 与 malformed metadata fail-closed；`iterable.sh` 验证当前
  near-sdk-rs Identity IterableMap/IterableSet 的 `P||v`/`P||m` exact bytes、index records、
  replacement/duplicate no-op、swap-remove、moved-index repair、reclamation 与 malformed rollback。
  `promise.sh` 部署 caller/receiver 两个合约，验证 batch function-call 的 UInt64 argument、
  `2^64+7` deposit 两个 limb、zero deposit、detached remote failure、caller panic 丢弃 receipt，
  余额不足的同步失败与 rollback，以及 returned call 的 exact 8-byte result、远端失败传播和
  caller/receiver receipt state 语义；还验证 detached `2^64+7` 与 returned `11` native transfer
  的 exact receiver balance delta，以及 max-u128 余额不足时 balance/state rollback；并验证外部
  predecessor 在读取 result 前被 `@[pf_near_private]` 完整 AccountId wrapper 以精确 panic
  拒绝且不改状态，并验证 private 先于 non-payable；`@[pf_near_payable]` 允许不读取 deposit
  的 donation-only mutator。真实 self callback 继续验证 exact Borsh UInt64 decode、独立
  callback argument、failed/oversized fallback；还验证两个
  有序 child join 的双成功以及左/右任一失败都仍执行 callback，且另一侧读取不被短路。
  `promise-result.sh` 另钉 ordinary call 的 result count 0 与越界 `promise_result` abort。
  `counter.sh` 还在初始化前验证 paid mutator 先命中 non-payable，普通 mutator/view 再以精确
  missing-state panic fail closed 且不创建 KV state；初始化后还对账 exact 16-byte schema
  envelope，随后重复初始化与算术场景照常通过。

CLI：`pf build --target near`。当前注册 `Counter`、`NearCtx`、`NearBytes`、`NearMemory`、
`NearOutput`、`NearStorage`、`NearVector`、`NearLookup`、`NearQueue`、`NearIterable`、
`NearPromise`、`NearPromiseResult`。
