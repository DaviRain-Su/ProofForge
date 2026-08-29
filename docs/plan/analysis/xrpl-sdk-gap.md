# XRPL SDK / Runtime 缺口（对标 SVM · EVM）

> 2026-08-29。权威排期仍是 [xrpl-runtime.md](xrpl-runtime.md)。
> 本文回答：SDK 组合层还差什么，以及那些组合依赖哪些 **本链 Runtime / host**。
> 不共享 SVM account bytes，不共享 EVM hashed slot。
>
> 链定位与「能不能做 Uniswap」见第 0 节。

## 0. 这是哪条链、能不能做 Uniswap

**不是侧链。** XLS-0101 WASM 智能合约的设计目标是进 **XRPL 主账本**（`ContractCreate` / `ContractCall` / `ContractData`）。
和这些不是一回事：

| | 是什么 | 本仓 |
|---|---|---|
| XRPL 主网今天 | 没有 `ContractCreate` | `deployable=false` |
| [AlphaNet](https://alphanet.xrpl.org) | 公开开发网，network_id **21337**，`SmartContract` 已开 | `--target xrpl-alphanet`（XLS-0102 host 名）。nerdnest 21465 DNS 已挂 |
| WASM Devnet | Smart Escrow 测试网 | **不是** 本 target（escrow `finish()`，不是 Contract SLE） |
| Bedrock 本地镜像 | 主账本形状的 rippled + wasm | **工程门** |
| [XRPL EVM Sidechain](https://www.xrplevm.org/) | Cosmos + EVM，XRP 当 gas | **不是** 本 target |
| Xahau / Hooks | 另一条链 / 账户钩子 | **不是** 本 target |

XLS 自己说：EVM 侧链给 Solidity 用；主账本 programmability 选 WASM，就是为了摸 XRPL 原生对象，而不是再桥一层。

**存储上限（今天的本仓 + 本镜像）：**

- 合约状态 = `ContractData` 里的 JSON 对象（命名 UInt64 槽）。
- 用户数据在设计里是 **每个用户一块** `ContractData`（`Owner` = 用户），不是 EVM `mapping(address => uint)` 的 keccak slot。
- 账本其它东西（XRP 余额、Trust line、AMM、NFT）**只读**；改它们要合约伪账户 **再提交一笔 XRPL 交易**（Payment / AMMDeposit…）。本仓还没有 `submitTransaction`。
- wasm v0 IR 拒绝 vector / map / loop。定长表可以先做成编译期 key `xs_0`…，或探针 `set_data_array_element_field`。

所以：

| 想做的 | 现在 | 要什么 |
|---|---|---|
| Ownable Counter / hash stamp | **已绿** | — |
| 定长登记表、小 AMM 的 2～3 个池槽 | **VEC-1 已绿**（编译期 `xs_0`…） | 更大表仍是源码展开，不是无界 Vec |
| Uniswap 式 `mapping(address => uint)` 余额 | **没有** | 用户 `ContractData` 或 JSON Map；再加 Amount |
| 真正的 swap（动 XRP / IOU） | **没有** | `submitTransaction` Payment / AMM；或读原生 AMM 对象 |
| 把 EVM Uniswap 字节码搬过来 | **永远不要** | 地址、slot、CALL 都不是 XRPL |

比赛若交 **「Lean 写出、本地 Bedrock 跑通的 WASM 合约」**：Ownable + 小状态机现在就能交。
若交 **「链上 Uniswap」**：要么走 EVM 侧链（Solidity），要么等本仓 VEC + 用户数据和/或原生 AMM 读/提交。不要承诺现在就能复刻 Uniswap v2。

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

没有：Map、Event、Payments。Access / Hash / 编译期命名槽（VEC-1）已绿。

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
| XRPL-VEC | 定长：编译期 JSON key `xs_0`…（array-element host 本镜像 trap） | 命名槽，暂不叫 `Storage.Vec`。**VEC-1 已绿** | 无界 `Array`、运行时长度、`set_data_array_element_field` |
| XRPL-MAP | **禁止** keccak / RBTree。先做编译期 key 的「命名槽表」。AccountId 键要另证：把三叶拼进 key 名，或 nested object | 以后才叫 `Storage.Map` | `HashMap`、动态 key 字符串、跨合约目录 |

定长命名槽不改 v0 子集：每个 `xs_i` 就是一个 UInt64 `State` 字段，走已有 `set_data_object_field`。
无界 Vec/Map 才是存储剖面升级，不能在 `Sdk.lean` 里假装有。

### 明确不做（本阶段）

- 把 SVM `Sdk.Storage.Map` / EVM `AddressMap256` 接到 XRPL
- wasm 里发 Payment / TrustSet（那是宿主交易）
- ERC-20 / SPL Token façade
- `delegatecall`、合约工厂、无界 heap
- 通用 wasmtime / 和 NEAR 共用 ValKind

## 6. 建议顺序

1. **SDK-ACCESS**（本刀）— 零新 host
2. **RT-2** parent hash + base fee — 镜像已有，形状同 ledger sqn
3. **探针** `set_data_array_element_field`（2026-08-29）：7 参数 import **能实例化**；
   调用写入 → `tecWASM_REJECTED`（wasm trap）。本镜像这条 host **不能当 Vec 物理层**。
   定长表改走编译期 JSON key `xs_0`…`xs_{n-1}`，仍用 `set_data_object_field`。
4. **VEC-1**（[wsm-012](../tasks/wsm-012.md)）：编译期 JSON key `xs_0`…`xs_2`，
   已绿。不依赖 array-element host。
5. Map 更后，且必须是 XRPL JSON 形状的设计，不是抄 EVM

官方 Rust WASM SDK（escrow 为主）的完整对照见
[xrpl-rust-sdk.md](xrpl-rust-sdk.md)。不要按 escrow `set_data` blob 来改本仓智能合约存储。

## 7. 验收句

- SDK 新名字不改变 host import 表，digest 只因 IR 形状变
- 任何 Map/Vec 提案必须写出：**key 怎么进 ContractJson**、**下标是不是编译期常量**、**缺字段返回什么**
- 缺 docker 的本地门 skip，不把 skip 当绿
