# ProofForge.Wasm.Near

## Purpose

WASM 家族的第二条链：**NEAR Protocol**。经 `Core.Target.Registration` 注册。
产物是 **`.wasm`**：Lean 直接 lowering 到 WAT，import 表钉 NEAR runtime 的
`env`（`input` / `register_len` / `read_register` / `storage_read` /
`storage_write` / `storage_remove` / `storage_has_key` / `value_return` /
`storage_usage` /
`panic_utf8` / `promise_batch_create` / `promise_and` / `promise_batch_then` /
`promise_batch_action_function_call` / `promise_batch_action_function_call_weight` /
`promise_batch_action_transfer` / `promise_return` /
`promise_results_count` / `promise_result`，按程序条件裁剪），组装器是锁定的
`wat2wasm 1.0.41`。外来叶子经
[`Wasm.Family`](wasm.md) fail closed。

基础标量绑定历史仓 proof_forge 的 profile `near-wasm-raw-u64-v1`：这**不是** JSON
ABI，也**不是** XRPL 的 C 参数 `i32`/`i64` export。标量 method 的 `env.input`
恰好为 `8 * paramCount` bytes little-endian。wsm-near-bytes-001 另为单个 `BoundedBytes` /
`BoundedString` 参数绑定 canonical Borsh `u32_le(length) || active bytes`（capacity 1..64；
String strict UTF-8）。wsm-near-output-001 使用 guest arena 为 bounded bytes/String 及单
limb unsigned array view 输出同样的 canonical active prefix；raw `UInt64` scalar view 仍恰好返回
8-byte little-endian。wsm-near-json-u128-output-001 binds only the exact two-leaf `UInt128` view
schema to one canonical quoted-decimal JSON string (`near-json-u128-string-v1`), reusing the event
decimal routine. wsm-near-json-u128-mutation-output-001 extends that same exact wire policy only to
an `Except Error (State × UInt128)` mutation: all state fields persist before one return, while a
failed branch traps and rolls back. Other two-field records and Promise-return combinations reject.
wsm-near-json-account-input-001 separately binds only the exact
compiler-owned `AccountId` parameter schema, on one-parameter views, to a bounded one-field
`{"account_id":"..."}` object subset. It is not a generic JSON codec or a public method claim.
wsm-near-json-u128-input-001 separately binds one exact `UInt128` parameter on view or mutating
wrappers to a canonical bounded `{"amount":"digits"}` subset. It preserves both limbs, accepts
digit-producing Unicode escapes, and rejects plus/leading-zero forms that near-sdk-rs accepts;
therefore it is a reusable parser prerequisite, not a serde-compatible/public FT ABI claim.
wsm-near-json-memo-input-001 adds compiler-owned `OptionalMemo16` and canonical `{}` /
`{"memo":null|string}` parsing. It preserves None versus Some-empty, decodes short/BMP/surrogate
JSON escapes plus raw UTF-8 into at most 16 bytes, and remains a closed prerequisite rather than a
generic serde wrapper.
wsm-near-json-message-input-001 adds compiler-owned `BoundedMessage64` and required canonical
`{"msg":"..."}` parsing for a later transfer-call path. It shares the memo Unicode string cursor,
but has independent exact 64-byte decoded, 426-byte wire, and 32-whitespace bounds. The diagnostic
fixture has no Promise effect or standard `ft_transfer_call` export.
wsm-near-json-ft-transfer-input-001 combines those value decoders behind one bounded field loop for
required `receiver_id`/`amount` and optional `memo`. All key permutations are accepted; duplicate,
unknown, escaped-key, and trailing forms reject. The compiler-owned 15-leaf frame is parser-only
and deliberately does not export or implement `ft_transfer`.
wsm-near-json-ft-transfer-call-input-001 extends that closed boundary with required `msg` in one
four-field any-order loop. Its exact 24-leaf frame preserves independent AccountId/u128/memo/message
geometry, and the 1179-byte wire bound accounts for worst-case escaping plus aggregate whitespace.
It remains parser-only: no `ft_transfer_call` export, ledger mutation, event, or Promise is implied.
wsm-near-json-ft-resolve-input-001 adds the separate exact 20-leaf `sender_id`/`receiver_id`/`amount`
frame needed by a future private resolver. Its bounded any-order field loop reuses the same
AccountId and quoted-u128 value decoders, while independent presence bits and zeroed 64-byte frames
keep the two identities isolated. It accepts at most 1079 wire bytes and 32 structural whitespace
bytes; the diagnostic fixture has no Promise result, ledger reconciliation, or standard export.
wsm-near-json-unit-output-001 binds only an explicit mutating `Unit` result to exact JSON `null`.
The four-byte `near-json-null-unit-v1` return is distinct from historical raw UInt64 output and
from an initializer's omitted return; it is the output prerequisite for the later transfer method,
not generic JSON serialization.
wsm-near-void-output-001 adds the distinct compiler-owned `pf_near_void` wrapper used by
near-sdk methods with an omitted result. `near-void-empty-v1` persists state but emits no
`value_return`, yielding exact empty SuccessValue bytes; explicit Unit remains JSON null.
wsm-near-ft-balance-of-001 composes those two exact policies into an exact `ft_balance_of` export
over the existing `BAL2` balance map. Missing and present-zero balances both return `"0"`, while
malformed present values trap; the bounded input grammar remains narrower than serde_json, so the
official-shaped view is not claimed as complete NEP-141 compliance.
wsm-near-ft-total-supply-001 adds the companion exact `ft_total_supply` export over the same
ledger state's two supply limbs. It returns canonical quoted u128, but ProofForge's existing
zero-parameter wrapper requires exactly empty input; near-sdk-rs ignores request bytes for methods
without arguments, so `{}` and arbitrary nonempty bodies are an explicit compatibility difference.
wsm-near-ft-transfer-001 integrates exact one-yocto, positive/non-alias, registered-account and
checked two-limb balance rules over the same `BAL2` ledger. It writes source then destination,
preserves supply and present-zero registration, emits one exact optional-memo NEP-141 event, and
returns empty bytes. Its argument object remains the bounded canonical subset above, so the exact
operation/output shape is not claimed as a fully serde-compatible public NEP-141 ABI.
wsm-near-ft-resolve-transfer-001 adds the exact private, non-payable `ft_resolve_transfer` export.
It requires one dependency result, clamps strict canonical quoted-u128 unused output, and reconciles
the same `BAL2` balances only after every read and arithmetic check. A present sender receives a
refund event and returns `amount - refund`; a deleted sender burns supply with memo `refund` and
returns the original amount, matching current near-contract-standards. Missing/present-zero receiver
paths are write-free. Callback arguments and Promise-result JSON remain bounded subsets narrower
than serde_json; the resolver itself remains a separately testable private callback.
wsm-near-ft-transfer-call-001 composes the exact payable `ft_transfer_call` export over the same
`BAL2` map: strict one-yocto/positive/non-alias/registered checks, two reads and all arithmetic
before source/receiver writes, one initial optional-memo transfer event, then the specialized
weighted child/private-resolver DAG. It returns the callback Promise after state persistence, so
the outer bytes are the resolver's exact quoted used amount. Real partial/full/malformed/failed
receipts pin reconciliation, event order, present-zero retention, supply conservation, and
rollback. Its 1179-byte bounded canonical argument subset remains narrower than serde_json, so the
exact operation and export do not imply complete public NEP-141 ABI compatibility.
wsm-near-storage-001 再以同一 arena staging byte-exact bounded raw
storage key/value，并保留 nearcore 0/1 status、stale register、present-empty 和 oversized
no-copy 语义。wsm-near-storage-key-001 仅把 internal raw storage key budget 拆分并扩到 72，
容纳 `Prefix4 || u32_le(64) || AccountId bytes`；value/result/public Borsh 仍限 64。
wsm-near-vector-001 在其上加入
`DirectVector64`：四字节 compile-time prefix、`prefix || u32_le(index)` key 与 standalone
Borsh UInt64 value；它 immediate-write，逻辑 length 仍由普通 ProofForge state 持有。
wsm-near-lookup-001 再加入 default-Identity `DirectLookupMap64` / `DirectLookupSet64`：key 为
`Prefix4 || Borsh(UInt64)`，map value 为 Borsh UInt64，set value 是 exact empty bytes。
wsm-near-u128-arithmetic-001 adds target-owned unsigned two-limb `NearToken` add/sub predicates
and carry/borrow result limbs. wsm-near-u128-mul-001 adds exact checked `NearToken × UInt64` using
two shared u64×u64 limb helpers; it is the arithmetic prerequisite for measured storage cost but
does not choose a byte price. `DirectAccountNearTokenMap` separately provides a closed default-Identity
AccountId-to-NearToken foundation with exact `prefix4 || u32_le(length) || active bytes` keys and
16-byte little-endian values. `Near.Sdk.Fungible.Ledger` interprets exact/missing balance snapshots
and registration status. Specialized slices compose that foundation into the bounded
official-shaped views, transfer, transfer-call, and private resolver described above; generic
public JSON ABI and automatic registration enforcement remain absent.
wsm-near-storage-economics-001 adds the real invocation-dynamic `env.storage_usage` u64 context
leaf. It deliberately exposes no `storage_byte_cost`: current near-sdk-rs/nearcore provide no such
host import, and protocol `storage_amount_per_byte` must come from explicit trusted network config.
wsm-near-storage-registration-001 composes that measured usage with checked full-width cost
arithmetic, the specialized AccountId map, attached deposit, and dynamic detached refund. The
closed policy registers only the nominal caller as present zero, measures its own variable key,
refunds positive excess, and depends on executing-receipt atomic rollback after speculative insert.
It is not a public NEP-145 ABI and does not make the ledger registration-enforcing.
wsm-near-storage-unregister-001 adds a separate strict-one-yocto caller-only removal policy. Only
an exact present-zero registration is removed; live reclaimed bytes are measured and refunded at
the same trusted price together with the guard yocto. Missing returns false and retains that yocto,
while malformed/nonzero entries reject before removal. This deliberately differs from current
near-sdk-rs's configured fixed-maximum refund; its base path excludes force-unregister/supply burn.
wsm-near-storage-force-unregister-001 integrates the same `BAL2` registration/balance map with
lossless total supply: nonzero removal requires explicit force and prechecked supply subtraction;
zero, mixed-limb, and max-u128 balances share the measured reclaim/refund path. Current
near-contract-standards directly reduces supply here without emitting `ft_burn`, so this closed
policy also emits no event and does not claim complete NEP-141/145 compliance.
wsm-near-u128-storage-001 adds exact 16-byte little-endian Borsh NearToken storage values and
strict status/fits/length-gated limb decoding; key geometry and ledger policy remain absent.
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
wsm-near-promise-ft-on-transfer-001 adds one specialized dynamic child-call boundary for the future
`ft_transfer_call` path. It stages the receiver's exact active AccountId bytes, composes exact
`{"sender_id":"...","amount":"...","msg":"..."}` bytes from a full nominal sender, two-limb
amount, and `BoundedMessage64`, then appends `ft_on_transfer` through nearcore's weighted host ABI
with zero deposit, gas 0, and weight 1. It returns only that child receipt after caller-state
persistence. It is not a generic dynamic JSON call and adds no callback, resolver, or standard
`ft_transfer_call` export.
wsm-near-promise-json-u128-result-001 adds a compiler-owned callback result frame that preserves
nearcore status and decodes only exact canonical quoted decimals (`"0"` or a nonzero decimal with
no leading zero) into valid plus two lossless limbs. Failed, oversized, malformed, noncanonical,
and overflowing results return invalid with zero limbs rather than trapping or exposing stale
register bytes. The private resolver owns the exact one-result/index-zero guard. This subset is
deliberately narrower than near-sdk-rs serde `U128`; the composed chain therefore remains narrower
than serde and still does not add a standard `ft_transfer_call` export.
wsm-near-promise-ft-resolve-chain-001 composes the dynamic weighted child with the fixed private
resolver: zero-deposit/gas weight-one `ft_on_transfer`, then a full-current-AccountId callback with
zero deposit, 5 Tgas, and weight zero. Independent checked arenas carry exact child and resolver
JSON, and only the callback receipt is returned after caller-state persistence. Real BAL2 sandbox
scenes cover partial/full/malformed/failed results and present/missing sender reconciliation. The
operation still performs no initial transfer and does not export `ft_transfer_call`.
wsm-near-init/payable/entry-policy/uninitialized-001 再钉入口生命周期：初始化器只成功一次，
private 先于 non-payable，参数解码后 ordinary state-consuming entry 必须见到 `STATE` marker，
否则精确 panic `The contract is not initialized`。这是类似 near-sdk-rs `PanicOnDefault` 的
ProofForge fail-closed 策略；不声称 near-sdk-rs 的普通 `Default` 也必然拒绝未初始化调用。
wsm-near-state-envelope-001 把 marker 收紧为 exact 16-byte
`PFNRST01 || fnv1a64(ordered slot schema)_le`；方法逻辑升级不改变 schema identity，而字段
name/width/ABI 或顺序变化会在任何 state/result read 前精确 fail closed。它是 ProofForge
split-key 元数据，不是 near-sdk-rs 的 Borsh `STATE`。
wsm-near-migration-001 在其上加入 `@[pf_near_migrate OLD_DIGEST]`：必须显式 private、
non-payable、零参数且每个程序最多一个。wrapper 只接受 exact old envelope，migration body
不能读取 current `State`，必须按旧 key 显式转换；成功时先写新字段、最后推进新 envelope。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Near.Ops` | NEAR context 值叶、static log、Promise/callback/result value/effect 与方言检查 | 其它链的方言、collection recipe |
| `Near.Host` | import 模块 `env`、digest 域 `near-raw-u64\|`、header | XRPL `host_lib`、Data blob sfield |
| `Near.Codec` | bounded bytes/String canonical Borsh, specialized quoted-u128 output, exact-schema AccountId/amount inputs, and compiler-owned optional memo/required message JSON inputs | generic JSON、general nullable/string schemas、multi-parameter JSON、collection layout |
| `Near.Memory` | invocation-local checked arena model、8-byte alignment、`memory.grow`/OOM 边界 | durable state、source-visible pointer、通用 malloc/free ABI |
| `Near.Sdk.Context/Access` | lossless context wrappers including dynamic storage usage、full-AccountId equality/self-call predicate | protocol-config storage byte price、general private/payable/init entry metadata |
| `Near.Sdk.NearToken` | checked unsigned u128 add/sub and exact u128×u64 predicates/result limbs | byte-price policy、balances、supply、public FT methods |
| `Near.Sdk.Transient` | compiler-erased `Buffer64` capacity 与 begin/set/get/finish 表面 | persistent Vector/Map/Queue、任意 raw pointer |
| `Near.Sdk.Storage` | internal raw key（1..72）、bounded value/result（1..64）、单 active result、status/length/fits/indexed-byte 表面、prefix ownership | 自动 prefix/hash、persistent collection layout、raw pointer |
| `Near.Sdk.Store.Codec` | shared fixed `Prefix4`、UInt32/UInt64 suffix、exact Borsh UInt64/NearToken values and strict result decode | AccountId keys、arbitrary `IntoStorageKey`、generic Borsh、ledger policy |
| `Near.Sdk.Store.Vector` | bounded `DirectVector64`、fixed `Prefix4`、官方 current Vector element key/value recipe | Rust `IndexMap` cache/Drop、`STATE` metadata、generic T、iterator/full `store::Vector` claim |
| `Near.Sdk.Store.Lookup` | direct Identity UInt64 map/set key/value recipe、get/has/put/remove raw status | Map cache/flush/old-value API、custom hashers、generic K/V、iteration/cardinality |
| `Near.Sdk.Fungible.Ledger/Registration` | exact/missing balance snapshots, checked ledger/transfer/resolver composition, measured caller register/unregister, and supply-integrated forced removal | generic public NEP-141/145 JSON ABI、arbitrary-account lifecycle、automatic registration enforcement |
| `Near.Sdk.Promises` | static detached/returned function call、static/full-AccountId native transfer、child→self callback、两个有序 child join、bounded result descriptor、strict Borsh UInt64 fallback decode | dynamic handles、arbitrary-N/nested joins、generic Borsh |
| `Near.IR` | registration、方言标签、target-owned bounded input/output frame 与 private/payable/migration policy binding | 程序形状、v0 子集、canonical 拼写（在 `Wasm.IR`） |
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
  round-trip、capacity 和 output UTF-8 failures；`json_account_input.sh` 验证 bounded
  `{"account_id":"..."}` view input 的 raw/escaped 2..64-byte decoding、九叶 carrier、exact
  433-byte wire/32-whitespace bounds 与 malformed object/string/account fail-closed matrix；
  `json_amount_input.sh` 验证 canonical `{"amount":"digits"}` 的完整两 limb decimal
  decode、digit Unicode escapes、exact 279-byte wire/32-whitespace bounds、mutating wrapper，
  以及 max+1/leading zero/plus/malformed object/string/decimal fail-closed matrix；
  `json_memo_input.sh` 验证 missing/null/Some-empty、short/BMP/surrogate/raw UTF-8 decode、
  decoded 16-byte/exact 139-wire/32 structural-whitespace bounds、inactive zeroing 与 malformed
  UTF-8/escape/object fail-closed matrix；
  `json_message_input.sh` 验证 required/empty message、shared Unicode decode、exact packed nine-leaf
  frame、64 decoded-byte/426-wire/32-whitespace bounds、mutating use 与 malformed matrix；
  `json_ft_transfer_input.sh` 验证三字段任意排列、required/optional/duplicate presence、完整
  AccountId/u128/memo leaves、exact 786-wire/32-whitespace geometry 与各 value decoder 的组合失败矩阵；
  `json_ft_on_transfer_input.sh` 验证 sender/u128/required-message 20-leaf receiver frame 的
  六种字段排列、Unicode/UTF-8、exact 1071-wire boundary、inactive zeros、stale isolation 与 rollback；
  `ft_receiver_value.sh` 验证 exact `ft_on_transfer` immediate-value 边界：full-u128 quoted
  amount、non-payable/parse rollback、state-before-output，以及真实 weighted child returned receipt；
  `promise_or_value.sh` 验证显式 `pf_near_promise_or_value` 的两条 state-first terminal：
  immediate quoted-u128 与真实 child `promise_return`，并钉住普通 u128/Unit/view 不获该能力；
  `json_ft_resolve_input.sh` 验证 two-AccountId/u128 20-leaf resolver frame 的六种字段排列、
  exact 1079-wire boundary、late failure/stale clearing 与 mutating parser rollback；`ledger.sh`
  additionally drives genuine child → private resolver receipts and checks result fallback/clamp,
  present-sender refund, deleted-sender burn, no-op branches, event/output bytes, and rollback，
  并对 exact `ft_transfer_call` 执行 initial transfer → weighted child → private resolver 的
  partial/full/malformed/failed returned chains、双 event 顺序、quoted output 与 supply conservation；
  `storage.sh` 验证 binary/empty keys、
  insert/replace/eviction、stale-register isolation、present-empty、oversized no-copy、remove/has；
  `vector.sh` 验证 exact current element keys/Borsh values、get/set/push/pop、capacity rollback
  与大 index 在 narrowing 前被拒绝；`lookup.sh` 验证 Identity map/set exact keys、map Borsh
  values、set empty values、insert/replace/remove status、namespace split 与 key reclamation；
  `queue.sh` 验证 ProofForge bounded FIFO 的 exact slots、wraparound、full/empty rollback、逐槽
  reclamation、drained head reset 与 malformed metadata fail-closed；`iterable.sh` 验证当前
  near-sdk-rs Identity IterableMap/IterableSet 的 `P||v`/`P||m` exact bytes、index records、
  replacement/duplicate no-op、swap-remove、moved-index repair、reclamation 与 malformed rollback。
  `promise.sh` 部署 caller/receiver 以及 test-only observer，验证 batch function-call 的 UInt64 argument、
  `2^64+7` deposit 两个 limb、zero deposit、detached remote failure、caller panic 丢弃 receipt，
  余额不足的同步失败与 rollback，以及 returned call 的 exact 8-byte result、远端失败传播和
  caller/receiver receipt state 语义；还验证 detached `2^64+7` 与 returned `11` native transfer
  的 exact receiver balance delta，以及 max-u128 余额不足时 balance/state rollback；dynamic
  AccountId transfer 另验证完整 predecessor receipt、2..64-byte geometry、只写 active bytes、
  inactive padding isolation 与 returned receipt propagation；并验证外部
  predecessor 在读取 result 前被 `@[pf_near_private]` 完整 AccountId wrapper 以精确 panic
  拒绝且不改状态，并验证 private 先于 non-payable；`@[pf_near_payable]` 允许不读取 deposit
  的 donation-only mutator。真实 self callback 继续验证 exact Borsh UInt64 decode、独立
  callback argument、failed/oversized fallback；还验证两个
  有序 child join 的双成功以及左/右任一失败都仍执行 callback，且另一侧读取不被短路；
  weighted dynamic `ft_on_transfer` additionally checks the exact full sender, mixed/high u128
  decimal, empty/control/Unicode/max-64 message JSON, zero attached deposit, inactive receiver
  padding isolation, returned result, and asynchronous missing-account failure semantics. Genuine
  child → private callback scenes also check canonical quoted-u128 zero/high/mixed/max decoding,
  malformed/noncanonical/oversized/failed invalid fallback, and repeated-call stale isolation.
  `promise-result.sh` 另钉 ordinary call 的 result count 0 与越界 `promise_result` abort。
  `bytes.sh` 还验证 arena-backed bounded dynamic `log_utf8` 对 empty/partial/full/multibyte
  active prefix 的精确 view logs，以及 malformed UTF-8 在日志效果前被拒绝；同一 gate 还
  对账 bounded NEP-297 string-data 的 compact envelope、metadata/data JSON escaping 与单次
  `log_utf8`。`ft_event.sh` 另对账 exact NEP-141 v1.0.0 `ft_mint`、`ft_transfer`
  与 `ft_burn`，包括完整 AccountId、官方字段顺序和 0 / 2^64 / 2^64+1 / max-u128 quoted
  decimal；三种 closed `WithMemo` API 把 bounded UTF-8 memo 放在 amount 后，覆盖 empty、
  quote/backslash/control、非 ASCII 与 16-byte 专用编译 capacity 边界，同时继续对账 no-memo 输出
  byte-exact 不变。每个效果只发一个 compact log；这不是 generic JSON ABI，也不实现余额、
  供应量、FT 方法或完整 NEP-141 合约。
  `token_arithmetic.sh` verifies checked two-limb carry/borrow and exact u128×u64, including both
  overflow paths and exact maximum boundaries, against near-sandbox without storage mutation.
  `token_storage.sh` verifies exact 16-byte Borsh token values, mixed/max/zero limbs, missing and
  malformed-length fallback, stale-result isolation, immediate writes and removal.
  `storage_economics.sh` verifies the real `storage_usage` host leaf around exact raw storage
  effects: stable positive views, same-size replacement, key/value growth, absent remove and full
  reclamation. It compares measured deltas and does not hard-code nearcore trie-record overhead.
  `counter.sh` 还在初始化前验证 paid mutator 先命中 non-payable，普通 mutator/view 再以精确
  missing-state panic fail closed 且不创建 KV state；初始化后还对账 exact 16-byte schema
  envelope，随后重复初始化与算术场景照常通过；同一 gate 还部署双字段升级代码，验证旧
  envelope 令 ordinary view fail closed、外部 migration 被 private guard 拒绝、同账户按
  `value` old key 转换后得到 exact 新字段/envelope、重复 migration 失败且新版本继续可写。

CLI：`pf build --target near`。当前注册 `Counter`、`NearCtx`、`NearBytes`、
`NearFungibleTokenEvent`、`NearTokenArithmetic`、`NearTokenStorage`、`NearMemory`、
`NearOutput`、`NearJsonUnitOutput`、`NearJsonU128Mutation`、`NearJsonAccountInput`、`NearJsonAmountInput`、`NearJsonMemoInput`、`NearJsonFtTransferInput`、`NearJsonFtOnTransferInput`、`NearFtReceiverValue`、`NearPromiseOrValue`、`NearJsonFtResolveInput`、`NearStorage`、`NearStorageEconomics`、`NearVector`、`NearLookup`、`NearQueue`、`NearIterable`、
`NearPromise`、`NearPromiseResult`、`NearMigration`。
