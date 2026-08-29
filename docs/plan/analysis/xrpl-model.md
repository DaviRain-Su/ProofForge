# XRPL WASM 是什么模型（对 EVM / SVM / NEAR）

> 2026-08-29。活网事实来自本仓 AlphaNet 探针（network_id **21337**）。
> 排期仍看 [xrpl-next.md](xrpl-next.md)。本文只回答：它长什么样、为什么不像 NEAR。

## 0. 一句话

EVM 是「合约地址里有一份持久存储」。
SVM 是「程序无状态，数据在交易带来的账户字节里」。
NEAR 是「每个合约账户自带 WASM + 持久 trie 存储 + 成熟 runtime 表」。
XRPL（XLS-0101）是「账本上本来就有 AccountRoot / Trust line / AMM；WASM 是一次 `ContractCall` 里跑的脚本，经 `host_lib` 摸这些对象，自己的小状态塞进 `ContractData` JSON」。

它支持 WASM，**不等于**它是一条 WASM 智能合约链。WASM 在这里是账本对象的扩展，不是世界计算机。

```diagram
EVM                         SVM                        XRPL (XLS-0101)
┌─────────────────┐         ┌─────────────────┐         ┌──────────────────────┐
│ 合约地址         │         │ ProgramId 无状态 │         │ 原生对象已经在账本里  │
│ keccak slot 树   │         │ 账户是数据袋     │         │ AccountRoot / AMM /  │
│ CALL 进别的合约  │         │ 交易带来账户列表 │         │ Trust line / NFT     │
│ 内存=本次调用    │         │ heap=本次调用    │         │ WASM=本次调用的脚本  │
└─────────────────┘         └─────────────────┘         │ JSON 槽=小本本       │
                                                        │ 改 XRP 要再提交 Payment│
                                                        └──────────────────────┘
```

## 1. 三张表

### 1.1 代码和状态住哪

| | EVM | SVM | XRPL WASM | NEAR |
|---|---|---|---|---|
| 代码 | 合约地址的 `code` | `.so` 在 Program 账户 | `ContractCreate` 挂 wasm | 合约账户的 WASM |
| 持久状态 | `storage[keccak(slot,key)]` | 账户**原始字节** | `ContractData.ContractJson` 命名字段 | 合约账户 trie（`storage_write`） |
| 本次调用内存 | EVM memory | 堆 / scratch | wasm 线性内存 | wasm 线性内存 |
| 调用结束堆还在吗 | 不在 | 不在（账户字节在） | **不在**：每次新建 VM（XLS-0102 §6.3） | 不在（trie 在） |

本仓 WAT：`(memory (export "memory") 1)`，64KiB，偏移钉死（0..19 Owner、20.. 参数、64+ 槽名）。那是 host 进出的 scratch，不是持久堆。SVM `BumpAllocator` 活在账户字节里，所以 Vec/Map 能跨交易；XRPL 不能把 bump 当 SDK 底座。

### 1.0 NEAR 也有线性内存——分配器不是 Map

NEAR 合约同样只有一块 wasm 线性内存。`near-sdk` 默认全局分配器是 **`wee_alloc 0.4.5`**
（`near-sdk/src/lib.rs`：`#[global_allocator] static ALLOC: wee_alloc::WeeAlloc`）。
它管的是本次调用里的 `Vec` / `String` / 序列化缓冲。

持久集合 **不** 住在这个堆里：

| 层 | NEAR | XRPL 今天 |
|---|---|---|
| 调用内堆 | `wee_alloc` → wasm linear memory | 固定偏移 scratch（无 malloc） |
| 持久 KV | `env.storage_write` / `storage_read`（host `env`） | `set_data_object_field` → `ContractData` JSON |
| `Vector` / `LookupMap` | 每个元素一个 **存储 key**（`prefix \|\| index`），`Drop` 时 `storage_write` | 没有任意 key 的 host；命名槽，Owner=caller |
| 跨 `ContractCall` 的指针 | **无效**。下次调用 `state_read` 重建 | **无效**。XLS-0102 每次新建 VM |

所以：NEAR 能做 Map，是因为 runtime 给了 **持久 trie**（`storage_write`），不是因为有了 `wee_alloc`。
把 `wee_alloc` 搬到 XRPL 只能得到更好的本次调用缓冲；`Sdk.Map` 仍然假。
XRPL 要对齐 NEAR 集合，缺的是 **任意 key 的持久 host**（或用户 ContractData），不是分配器。

Lean 合约也不走 Rust `#[global_allocator]`：本仓发射 WAT 直接写死偏移，不链 wee_alloc。

### 1.2 钱和别人怎么动

| | EVM | SVM | XRPL WASM |
|---|---|---|---|
| 转原生币 | `call{value}` 改账户余额 | System CPI | wasm **不能**改 XRP；要 `submitTransaction` Payment |
| Token | ERC-20 也是合约存储 | SPL = 账户字节 + mint | IOU / MPToken **就是** Trust line，不是再发一套 ERC-20 |
| 调别人 | `CALL` / `DELEGATECALL` | `sol_invoke` | 没有成熟「合约调合约」；跨对象靠 host 读 + 再提交交易 |
| 日志 | LOG → receipt | `sol_log` / return data | `trace_num` = rippled **调试打印**，共识不索引（本仓 AlphaNet poke=0，不开 Sdk.Log） |

### 1.3 本仓量到的写权限（AlphaNet 21337）

| 写到谁 | `set_data_object_field` |
|---|---|
| `tx_field(sfAccount)` = **caller** | 绿：`bal=1` 挂在 caller 的 ContractData |
| `home_le_field(sfContractAccount)` = **合约** | **拒** `tecBYTECODE_REJECTED` / VM **-22** |

今天 Counter / Ownable / Pausable 其实是「**调用者名下的一张 JSON 卡片**」，不是「合约金库」。EVM Uniswap 的大表在合约存储里；这里没有那张表。`mapping(address => uint)` 没有物理层：不能换 Owner 到合约再按地址分槽，也不能用 wasm 堆。

`cache_le` import **能实例化**；零 32B id 调用返回 **-10**（对象不存在）。host 在，还没读到 AccountRoot.Balance。

## 2. 设计意图（为什么长这样）

XLS 自己的分工：

- **XRPL 主账本**：支付、DEX、AMM、NFT、IOU 已经是一等对象。WASM 用来 **摸这些对象**，加条件，而不是再造一个 EVM。
- **XRPL EVM Sidechain**（2025-06 主网）：给 Solidity / 通用合约。那是另一条链。
- **Smart Escrow**（XLS-100）：WASM 只决定一笔托管能不能 `finish()`。官方 Rust SDK 主要是这个，不是 `ContractCall`。
- **主网今天**：没有 `ContractCreate`。`SmartEscrow` amendment 仍 In Development。本仓 `deployable=false`。

所以生态「不像 NEAR」不是因为 WASM 字节码差一截，是因为 **产品目标就不是「链上任意 dApp」**。通用合约被放到 EVM 侧链；主账本 WASM 是窄的、对象级的。

## 3. 为什么 XRPL 的 WASM 生态不像 NEAR（或 CosmWasm）

NEAR 2018 主网就是 WASM 合约链：每个账户一份代码 + 持久存储 + 稳定 `env.*` + `near-sdk` + 钱包 / explorer / 多年主网资金。开发者实现的是 **应用**，不是 runtime。

XRPL 主账本 WASM 是另一条时间线和另一套合同：

| | NEAR | XRPL 主账本 WASM |
|---|---|---|
| 主网合约 | 2018 起 | **还没有** `ContractCreate` |
| 公开能跑的网 | mainnet / testnet | AlphaNet（本仓 21337，`3.3.0-rc1`）；旧 nerdnest 21465 已死 |
| Runtime 表 | 多年稳定 `env`（含 `storage_write`） | Bedrock 本地名 ≠ XLS-0102 名；本仓要两套 host |
| 分配器 | `wee_alloc`，**仅本次调用** | 固定 scratch；不要搬 wee_alloc 当 Map |
| 持久存储 | 合约 trie，任意 key | JSON 命名槽；合约当 Owner 被拒 |
| SDK | `near-sdk-rs` 覆盖存储/Promise/集合 | 官方 crate **以 escrow 为主**；智能合约 façade 薄 |
| 钱 | 合约账户有余额，能转 | 改 XRP 要再提交 Payment；wasm 里 `x +=` 不动链上 XRP |
| 工具 | `near-cli`、sandbox、钱包 | Bedrock CLI ≠ AlphaNet；公开 RPC 对带 Parameters 的 Call **HTTP 502** |

因此「都得自己实现」是真的，而且该自己实现的是 **host 探针和账本形状**，不是再写一个 bump allocator 或抄 EVM Map。NEAR 生态完善，是因为它把「合约=账户+存储+runtime」做了八年；XRPL 把「合约=世界计算机」放到了侧链，主账本这条腿 2025-11 才上 AlphaNet，ABI 还在改名（`cache_ledger_obj` → `cache_le`）。

本仓必须自建的，NEAR 开发者通常买现成的：

1. **host 表**（Bedrock vs AlphaNet 两套名字）
2. **存储 Owner 规则**（只能写 caller）
3. **部署路径**（`wat2wasm` + 自签 `ContractCreate`，不是 `near deploy`）
4. **零参数活网**（Parameters 502）
5. **原生对象读写**（`cache_le` / `submitTransaction`）——还没绿

Lean → WAT → `.wasm` 只解决「怎么出字节码」。生态缺口在 runtime 合同，不在编译器。

## 4. 对 ProofForge 的后果

- 学 EVM/SVM 的 **分层**（Runtime 叶 → SDK `pf_inline` → Example），不学 keccak / 账户字节 / CPI。
- 不要 wasm 分配器当 SDK 底座（[xrpl-next.md](xrpl-next.md) §1.1）。
- 不要 `Sdk.Map` / `Sdk.Payments` / `Sdk.Log`，除非对应 host 探针绿。
- 比赛交「Lean 写出、AlphaNet 跑通的状态机」现在可以；交「链上 Uniswap」要么走 EVM 侧链，要么等用户 ContractData + Payment。
- NEAR 线（PR #5）各自拥有 `env` 表，不要和 XRPL 共用 ValKind。

## 5. 活网钉子（不要 rediscover）

- RPC `https://alphanet.xrpl.org`，network_id **21337**，`SmartContract` 开
- 创世种子 `snoPBrXtMeMyMHUVTgbuqAfg1SUTb` → `rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh`
- 存储写 caller 绿、写合约账户 **-22**
- `trace_num` poke=0（调试日志）
- `cache_le` 能实例化，零 id **-10**
- 公开 `submit` 带 Parameters → HTTP 502
