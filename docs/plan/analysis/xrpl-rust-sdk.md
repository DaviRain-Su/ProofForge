# 官方 Rust WASM SDK vs ProofForge XRPL

> 2026-08-29。对照 [ripple/xrpl-wasm-stdlib](https://github.com/ripple/xrpl-wasm-stdlib)
> （`xrpl-common-stdlib` + `xrpl-escrow-stdlib`）。Bedrock 是 CLI，不是另一套合约 SDK。
> 本仓缺口排期仍以 [xrpl-sdk-gap.md](xrpl-sdk-gap.md) 为准。

## 1. 先分清两套东西

官方 crate **主要是 Smart Escrow**：条件支付、几乎只读账本、唯一可变的是当前 escrow 的 `Data` blob。
例子全在 `examples/smart-escrows/`（hello_world / oracle / kyc / notary / nft_owner / ledger_sqn）。

ProofForge 的 XRPL target 是 **XLS-0101 Smart Contract**（Bedrock `ContractCall`）：
有 `caller` / `self`、把 `State` 写进 `ContractData.ContractJson`。
官方 `main` **没有** 成熟的 `ContractCallContext`，也没有 `set_data_object_field` 的公开 façade。

所以：不能按「把 Rust SDK 逐函数抄进 Lean」来做。该学的是 **host 能力分层**；
合约形状我们已经比官方 escrow SDK 更靠智能合约一侧。

```diagram
官方 Rust（escrow）              ProofForge XRPL（contract）
┌─────────────────────┐        ┌──────────────────────────┐
│ finish() → i32      │        │ export initialize/bump   │
│ 读 tx / 读 SLE      │        │ caller/self + JSON 槽    │
│ 偶尔 set_data blob  │        │ 状态码 0/1/2/3           │
└─────────────────────┘        └──────────────────────────┘
         │                                │
         └──────── host_lib ──────────────┘
              名字因镜像而异
```

Bedrock 镜像用的是 `get_tx_field` / `get_data_object_field` / `compute_sha512_half`，
不是新 stdlib 的 `tx_field` / `sha512_half` / `parent_ldgr_hash`。接线以本镜像为准。

## 2. 官方 SDK 有什么（合约能调用的面）

### 共享（`xrpl-common-stdlib`）

| 类 | 公开名 | 降到 host（stdlib 名；本镜像可能不同） |
|---|---|---|
| 链元数据 | `ledger_sqn` / `parent_ledger_time` / `parent_ledger_hash` 32B / `base_fee` / `amendment_enabled` | `ldgr_index`、`parent_ldgr_time`、`parent_ldgr_hash`、`base_fee` |
| 当前交易 | `tx.get_account`、fee/seq/flags/…、任意 `SField`、blob | `tx_field` / `tx_inner` / `tx_arr_len` |
| 账本对象 | `cache_le` + 槽；AccountRoot / Oracle / NFT…  typed 读 | `cache_le`、`le_field`、`le_inner` |
| 路径 | `.path().field().index(i).get::<T>()` | locator + nested/array 读 |
| 密码 | `sha512_half(&[u8]) → [u8;32]`、`check_sig` | `sha512_half`、验签 host |
| 日志 | `trace` / `trace_num` / `trace_acct` / `trace_amt` | `trace_*` |
| 类型 | `AccountID` 20B、`Amount`（XRP/IOU/MPT）、NFT 分解、keylet | 纯值 + ID 构造 host |
| 浮点 | `float_add` 等 xfloat | 本阶段不碰 |

### Escrow 专有（`xrpl-escrow-stdlib`）

| 名 | 作用 |
|---|---|
| `EscrowFinishContext` | `tx()` + `escrow()` |
| `FinishResult` | succeed / reject |
| `set_data(&[u8])` | **整块替换** 当前 escrow `Data` |
| `EscrowStorage` encode/decode | 在那块 blob 上序列化 |

没有：任意 SLE 写入、JSON 对象字段写、数组 push、Payment 从 wasm 发出。

## 3. ProofForge 已经对上的

| 官方 | 本仓 | 差在哪 |
|---|---|---|
| `ledger_sqn` | `Context.ledgerSqn` | 我们是 UInt64 零扩展，他们 `u32` |
| `parent_ledger_time` | `Context.parentTime` | 同 |
| `parent_ledger_hash` 32B | `Context.parentHashLo` | **我们只露首个小端 u64** |
| `base_fee` | `Context.baseFee` | 同；不是 EVM 256 |
| `sha512_half` 任意缓冲 | `Hash.sha512HalfLit "ascii"` | **只有编译期 ASCII** |
| `tx.get_account` | `Context.caller` 三叶 | 他们是完整 20B 类型；我们拆三叶 |
| escrow `Data` blob | `ContractJson` UInt64 槽 | **完全不同的持久化**；我们更像智能合约 |

官方没有、我们有：`Context.self`、`Access.requireOwner`、按槽 `set_data_object_field`。
这是 Bedrock 智能合约 ABI，不要为对齐 escrow 而拆掉。

## 4. 若「对接官方 SDK 能力」，按层要做什么

只列 **智能合约 target 用得上、且本镜像已有或可探针的**。Escrow `finish()` 不是本 target。

### A. 纯组合 / 已有 host（可做）

| 项 | 说明 |
|---|---|
| `parentHash` 完整 32B | host 已写 32B，现在只取 w0。四叶或 Bytes32 要改 view ABI，先别 |
| `trace_num` | 镜像有字符串。先本地探针：会不会当共识副作用 |
| 动态 `sha512_half` | 镜像 `compute_sha512_half` 已接字面量。运行时缓冲要 IR 允许字节槽 |

### B. 读账本（官方主菜，我们几乎没有）

这是 Rust SDK 真正大的面。依赖 `cache_le` + 槽 + `SField`，不是 SDK 里编一个 `Map`。

| 切片 | Runtime | 本镜像线索 |
|---|---|---|
| 读任意 AccountRoot | `cache_le(accountroot_id)` + `le_field` | 镜像有 `get_ledger_obj_field` 等名，**未探针** |
| 读当前 tx 更多字段 | `get_tx_field` 已有；扩 sfield 表 | 已用 `sfAccount`；fee/seq 可试 |
| 嵌套 / 数组读 | `*_nested_field` / `*_array_len` | 镜像字符串在，未探针 |
| Oracle / NFT / Trust line | 先有 cache + 路径，再 SDK 名 | 后 |

没有 `cache_le` 探针绿，不要做 `Sdk.AccountRoot.balance`。

### C. 写存储（官方弱、我们强、形状不同）

| 官方 | 本仓该走 |
|---|---|
| escrow `set_data` 整 blob | **不要**当智能合约存储（本镜像 `update_data` 不落账本） |
| 无 JSON 字段写 | 已有 `get/set_data_object_field` |
| 无数组写 | 镜像有 `set_data_array_element_field` → **VEC 探针** |
| 无 nested 写 | `set_data_nested_object_field` → 记录，不是 Map |

Vec/Map 仍然是 XRPL JSON 形状，禁止抄 SVM RBTree / EVM keccak。

### D. 明确不要对接

- `#[smart_escrow]` / `FinishResult` / 整个 escrow 对象可变 `Data`
- 从 wasm 发 Payment / TrustSet
- 把 `Amount::IOU` 做成 EVM ERC-20
- stdlib 新名字（`parent_ldgr_hash`）替换本镜像旧名
- 完整 xfloat 算术（除非有合约刚需）

## 5. 建议顺序（接 [xrpl-sdk-gap.md](xrpl-sdk-gap.md)）

1. **探针** `set_data_array_element_field`（定长 Vec 能不能落 JSON）
2. **探针** `trace_num`（日志是否可当工程门）
3. **探针** `cache_le` / `get_ledger_obj_field`（能不能读别的 AccountRoot）
4. 绿了再开 Runtime 叶，SDK 只 `pf_inline`
5. `check_sig` / 完整 32B hash / Amount 三变体更后

验收：每个官方名必须落到 **本镜像已确认的 host 字符串**；stdlib 文档和 Bedrock 二进制不一致时，信二进制。
