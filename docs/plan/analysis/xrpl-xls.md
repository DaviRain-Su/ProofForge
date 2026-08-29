# XLS 标准 vs ProofForge：不是每份 RFC 都用 WASM 实现

> 2026-08-29。XLS 目录约 **78** 份（xls.xrpl.org）。主网 amendment 快照
> 2026-08-18（[known-amendments.md](https://xrpl.org/resources/known-amendments.md)）。
> 本文回答：像 XLS-30 这种「原生对象」有多少、我们实现了几个、还要不要全做。

## 0. 先分两堆

| 堆 | 谁实现 | 我们做什么 |
|---|---|---|
| **协议对象**（XLS-30 AMM、XLS-20 NFT…） | **rippled C++** + 验证者投票开 amendment | **不重写。** WASM 以后只读 / 再提交对应交易 |
| **WASM 可编程**（XLS-100/101/102） | 还在 Draft / In Development | 本仓的 target：**出 `.wasm` + host 表** |

「主账本已经有 AMM」= 第一堆已经在跑。  
「WASM 卡片写不出共享池」= 第二堆没有程序金库。  
两堆都对，不要用 WASM 把第一堆再实现一遍。

## 1. 本仓已经对齐的 XLS（WASM 腿）

| XLS | 我们做到哪 | 没做 |
|---|---|---|
| **0101** Smart Contracts | AlphaNet `ContractCreate` / `Call`、用户 `ContractData` 卡片、`pf deploy` | 主网 `deployable=false`；合约当 Owner **-22**；`setUserData(别人)` 未证 |
| **0102** WASM VM | 锁定 `wat2wasm`；两套 host 名（Bedrock / AlphaNet）；`trace_num` / `cache_le` 探针 | 完整 host 表、`submitTransaction`、view i32/i64 分网 |
| **0100** Smart Escrows | **明确不做**（`finish()` 不是 ContractCall） | 官方 Rust SDK 主菜；别抄 `set_data` blob |

这不是「实现了 3 个 RFC 的全部条款」，是 **编译器 target 用到的那几条 host**。

## 2. 主网已开的「像 XLS-30」的协议对象（不要用 WASM 重写）

这些是账本交易 + SLE，公式在 C++。任何人发 tx，不经过我们的合约。

| XLS | 主网 | 对象 / 交易 | ProofForge |
|---|---|---|---|
| 账本本身（无编号） | 多年 | AccountRoot、Payment、OfferCreate、TrustSet、Escrow、PayChan | 以后 `submitTransaction` / `cache_le` |
| **20** NFT | 已开（V1_1） | NFTokenMint / Offer / Accept | 读 NFT 对象；别用 JSON 仿一套 NFT |
| **30** AMM | **2024-03-22 已开** | AMMCreate / Deposit / Withdraw / Payment | 读 AMM SLE；发 AMMDeposit。**不要** WASM Uniswap |
| **33** MPT | MPTokensV1 已进协议（V2 DEX 仍开发中） | MPTokenIssuance | 当资产类型读，不重做发行 |
| **39** Clawback | 已开 | 发行人收回 IOU | 不实现 clawback 引擎 |
| **40** DID | Final / 已有 DIDSet 类 | DID 对象 | 不重做身份层 |
| **47** Price Oracle | Final | OracleSet / PriceOracle | 只读报价；别在卡片里做预言机 |
| **52** NFTokenMintOffer | Final | 铸造时带卖单 | 不重做 |
| **56** Batch | Final；主网 BatchV1_1 仍在投票 | 原子多笔 | 不是 WASM 循环 |
| **70** Credentials | Final | 凭证对象 | KYC 读字段，不重做 |
| DEX / IOU | 多年 | Offer、Trust line | 原生路径；不要 ERC-20 façade |

还在投票或开发、同样是协议对象（仍不是我们的活）：

| XLS | 状态（2026-08） | 我们 |
|---|---|---|
| **38** Bridge | 投票中 ~11% | 侧链桥，不是 WASM target |
| **65** Vault | 投票/开发 | 单资产金库 SLE |
| **66** Lending | 投票/开发 | 借贷 SLE |
| **82** MPT DEX | In Development | MPT 进 DEX |
| **100** SmartEscrow | In Development | 本仓不做 escrow target |

xls.xrpl.org 上还有大量 Ecosystem / System（钱包 URI、元数据、CTID…）。那些不是账本对象，更不是 WASM 工作。

## 3. 要不要「都实现」？

**不要。** 78 份 XLS 里，Amendment 约 46 份。ProofForge 的 XRPL target 只拥有：

1. **出 wasm**（0101/0102 的编译腿）
2. **host 探针**：能读哪些 SLE、能提交哪些 tx
3. **用户卡片状态机**（每人一份的逻辑）

协议对象已经由 rippled 实现。我们若「实现 XLS-30」= 在 WASM 里再造一个池子 = 和主网 AMM **抢流动性**，而且存储模型还不让写金库。

对接优先级（有 host 才开 Runtime 叶）：

| 优先级 | 对象 | 为什么 |
|---|---|---|
| P0 | Payment、AccountRoot.Balance | 真动 XRP / 读余额 |
| P1 | AMM（XLS-30） | 兑换走原生池，不走 Uniswap 克隆 |
| P2 | Offer / Trust line | DEX 路径 |
| P3 | NFT、Oracle、Credential | 只读场景 |
| 不做 | Vault/Lending 的 C++ 引擎、Bridge、Escrow finish、侧链 EVM | 不是本 target |

## 4. 一句话

XLS-30 这种标准 **已经在主网跑**，实现者是 rippled，不是我们。  
我们实现的是 **WASM 怎么摸这些对象**。摸之前要 `cache_le` / `submitTransaction` 绿。  
没绿之前，不要把 78 份 RFC 开成任务卡。
