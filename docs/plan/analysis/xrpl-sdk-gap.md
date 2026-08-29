# XRPL SDK / Runtime 缺口（对标 SVM · EVM）

> 2026-08-29。权威排期仍是 [xrpl-runtime.md](xrpl-runtime.md)。
> 本文回答：SDK 组合层还差什么，以及那些组合依赖哪些 **本链 Runtime / host**。
> 不共享 SVM account bytes，不共享 EVM hashed slot。

## 1. 三层，不要混

```diagram
┌──────────────────────────────────────────────┐
│ 合约 Examples                                 │
│ 普通 Lean + @[pf_entry]                       │
└─────────────────────┬────────────────────────┘
                      │
                      ▼
┌──────────────────────────────────────────────┐
│ SDK  组合已有 Runtime，@[pf_inline]            │
│ Context / AccountId.eq / Access / Hash        │
│ 不新增 host、不新增 Op                        │
└─────────────────────┬────────────────────────┘
                      │ unfold
                      ▼
┌──────────────────────────────────────────────┐
│ Runtime  本链叶子                              │
│ caller20 / self20 / ledgerSqn / sha512HalfLit │
└─────────────────────┬────────────────────────┘
                      │
                      ▼
┌──────────────────────────────────────────────┐
│ Host  本 Bedrock 镜像的 host_lib               │
│ get_tx_field / set_data_object_field / …      │
└──────────────────────────────────────────────┘
```

| 问题 | 层 |
|---|---|
| 链上有没有这条 syscall？ | **Runtime / Host** |
| 普通 Lean 名能不能组合已有叶子？ | **SDK** |
| 状态是 JSON 槽、账户字节、还是 keccak slot？ | **物理模型，链拥有** |

CMP（wsm-006）是 Runtime 能力：三叶能比。SDK 的 `AccountId.eq`（wsm-009）只是把那棵 `if` 收成名字。

## 2. 现在有什么

### Runtime（本镜像已接线）

| Lean | host |
|---|---|
| `xrplCaller20` 三叶 | `get_tx_field(sfAccount)` |
| `xrplSelf20` 三叶 | `get_current_ledger_obj_field(sfContractAccount)` |
| `xrplLedgerSqn` | `get_ledger_sqn` |
| `xrplParentTime` | `get_parent_ledger_time` |
| `xrplSha512HalfLit "…"` | `compute_sha512_half`，只回首个小端 UInt64 |

存储：每个 `State` 的 UInt64 槽 → `ContractData.ContractJson` 一个 key。不是 Map。

### SDK（已绿）

| 名 | 展开成 |
|---|---|
| `Context.caller / self / ledgerSqn / parentTime` | Runtime 叶 |
| `Hash.sha512HalfLit` | `xrplSha512HalfLit` |
| `AccountId.eq` / `ofLimbs` | 三叶嵌套 `if` |

没有：Access 门面、Vec、Map、Event、Payments。

### wasm v0 子集（现在卡住 Vec/Map 的原因）

`Wasm.IR` 拒绝 loop / local / **vector** / **map** / 位运算。
Lean `Vector` 状态、动态下标、`HashMap` 现在抽出即 fail closed。
所以「SDK 里加个 Map」**不能**只写 `pf_inline`：要先开存储形状和 IR。

## 3. 对标 SVM / EVM：学分层，不学物理模型

| 能力 | SVM | EVM | XRPL 该落在哪 |
|---|---|---|---|
| caller / self | `Account` / signer | `Context.caller` `Addr20` | **已有** `AccountId` 三叶 |
| 相等 | 32B 按字 | `Address.eq` → `eq20` | **已有** `AccountId.eq` |
| 权限门 | 应用自己比 | `Access.requireOwner` | SDK 组合，**下一刀** |
| 时钟 | `clockSlot` sysvar | `blockNumber` / `timestamp` | 账本序号 / parent time，**已有** |
| hash | `sha256Lit` / keccak | keccak256 | SHA-512Half 字面量，**已有**；动态输入仍 FC |
| 持久标量 | 账户字 | static slot | JSON UInt64 槽，**已有** |
| 定长 Vec | 账户 stride + 容量 | `State` 里 `Vector` → 连续 slot | **没有**。物理模型应是编译期 key `xs_0`…`xs_{n-1}`，不是账户 stride |
| Map | 账户内 ordered RBMap | keccak hashed namespace | **没有**。禁止抄 keccak / RBTree。候选：编译期 JSON key，或本镜像的 nested object field |
| 日志 | `sol_log` / return data | LOG / revert selector | 镜像有 `trace_num` / `trace_account`，**未接线** |
| 转账 | System CPI | `Payments` CALL | XRPL Payment 是宿主交易，**不是** wasm 里随便转。v0 不做 |
| Token | SPL CPI | ERC-20 closed call | 无。XRPL IOU / MPToken 是账本对象，要另开 Runtime |

SVM Map 活在 **account bytes + 编译期 region**。
EVM Map 活在 **keccak(slot, key)**。
XRPL 持久状态今天是 **ContractJson 的命名 UInt64 字段**。
三条物理模型不能共用一个 `Sdk.Map`。

## 4. 本镜像有、但 Runtime 还没接的 host

在 `lejamon/rippled_smart_contract_vault_x86` 的 `rippled` 字符串里确认过。
XLS-0102 的 `home_le_field` / `sha512_half` **不是** 本镜像名字。

| host | 签名（从现有同类推断 / stdlib 同形） | 用途 | 优先级 |
|---|---|---|---|
| `get_parent_ledger_hash` | 缓冲 32B | 父账本 hash，对标 SVM 不提供的 blockhash；XRPL 身份是 SHA-512Half | RT-2 |
| `get_base_fee` | i32 | 费，不是 EVM `baseFee` 256 | RT-2 |
| `get_tx_nested_field` / `get_tx_array_len` | 已有 `get_tx_field` 的内层 | 读 tx 内嵌字段 / 数组长 | 后 |
| `get_current_ledger_obj_nested_field` / `*_array_len` | 内层 / 数组 | 读 Contract SLE 内层 | 后 |
| `get/set_data_nested_object_field` | 嵌套 JSON 对象 | **嵌套记录**，不是 Map | 存储-1 候选 |
| `get/set_data_array_element_field` | 数组下标 | **定长 Vec** 候选 | 存储-1 候选 |
| `trace_num` / `trace_account` / `trace_amount` | 调试/日志 | 不是 EVM LOG，共识是否落账本未证 | 先探针，再开 |
| `update_data` | blob | **本镜像不落账本**，继续禁 |

未接线就不许 SDK 假装有。

## 5. SDK 还差什么（按依赖排）

只能这个方向：没有叶子，就不要门面；没有存储形状，就不要 Vec/Map。

### 现在就能做（纯组合，不新 host）

| 切片 | 内容 |
|---|---|
| **XRPL-SDK-ACCESS** | `Access.requireOwner (owner : AccountId) : Bool` = `AccountId.eq Context.caller owner`。Ownable 走它 |
| 两步移交 | 一个 pending 三叶，源码 `if`，仍不是新 Op |
| owner+hash | `requireOwner` 之后写 `Hash.sha512HalfLit` |

这些证明 SDK 是组合层，不是新链。

### 要先开 Runtime 再做 SDK

| 切片 | Runtime | SDK 名 | 不做 |
|---|---|---|---|
| XRPL-RT-2（[wsm-011](../tasks/wsm-011.md)） | `xrplParentHashW0` 首 u64；`xrplBaseFee` | `Context.parentHashLo` / `baseFee` | 完整 32B 当返回值 |
| XRPL-LOG | 仅当本地证明 `trace_*` 不破坏共识 | `Log.num` | EVM LOG3 / event ABI |
| XRPL-VEC | 定长：要么连续 JSON key，要么 `*_array_element_field`；IR 允许编译期下标 | `Storage.Vec n` | 无界 `Array`、运行时长度 |
| XRPL-MAP | **禁止** keccak / RBTree。先做编译期 key 的「命名槽表」。AccountId 键要另证：把三叶拼进 key 名，或 nested object | 以后才叫 `Storage.Map` | `HashMap`、动态 key 字符串、跨合约目录 |

Vec/Map 是 **存储剖面升级**，不是在 `Sdk.lean` 里加函数。要改 `Wasm.IR` v0 子集和发射器的 key 布局。

### 明确不做（本阶段）

- 把 SVM `Sdk.Storage.Map` / EVM `AddressMap256` 接到 XRPL
- wasm 里发 Payment / TrustSet（那是宿主交易）
- ERC-20 / SPL Token façade
- `delegatecall`、合约工厂、无界 heap
- 通用 wasmtime / 和 NEAR 共用 ValKind

## 6. 建议顺序

1. **SDK-ACCESS**（本刀）— 零新 host
2. **RT-2** parent hash + base fee — 镜像已有，形状同 ledger sqn
3. **探针** `set_data_array_element_field` / nested object：本地写一个下标，读回来。失败就停
4. 探针绿了再开 **VEC-1**（定长 UInt64 向量，编译期 `n`）
5. Map 更后，且必须是 XRPL JSON 形状的设计，不是抄 EVM

## 7. 验收句

- SDK 新名字不改变 host import 表，digest 只因 IR 形状变
- 任何 Map/Vec 提案必须写出：**key 怎么进 ContractJson**、**下标是不是编译期常量**、**缺字段返回什么**
- 缺 docker 的本地门 skip，不把 skip 当绿
