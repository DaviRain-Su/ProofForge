# XRPL 下一阶段：复杂合约还差什么

> 2026-08-29。HEAD `190f543`（wsm-017）。本文是 **wsm-018+** 的排期，
> 接 [xrpl-sdk-gap.md](xrpl-sdk-gap.md) / [xrpl-runtime.md](xrpl-runtime.md)。
> 学 EVM/SVM 的分层，不学 keccak slot / account bytes / CPI。

## 0. 现在能写什么样的合约

活网（AlphaNet 21337，零参数）已经能组合：

| 合约 | 能力 |
|---|---|
| `XrplSmoke` | 无权限 Counter |
| `XrplGate` | Ownable + `renounce`（状态码 3） |
| `XrplHold` | Ownable + Pausable（状态码 4） |
| `XrplMark` | owner 门后写 SHA-512Half 字面量 |
| `XrplVec` | 编译期 3 槽表（Bedrock 本地；活网带参 502） |

这不是「只有一个 Counter」。这是 **单合约、命名 UInt64 槽、无循环、无用户目录**
的状态机。EVM 的 Vault / ERC-20 / Uniswap 和 SVM 的 Token / Phoenix 都靠
**另一套物理模型**，抄名字没用。

```diagram
今天能做                         还不能做
┌─────────────────────┐         ┌──────────────────────────┐
│ 几个 UInt64 JSON 槽  │         │ 每用户一块余额            │
│ owner / pause / hash │         │ 读别人的 AccountRoot      │
│ 3 槽定长表 xs_0..    │         │ 从 wasm 发 Payment / AMM  │
│ 零参数活网           │         │ 运行时 Vec / 动态 key     │
└─────────────────────┘         └──────────────────────────┘
```

## 1. 卡在哪一层（不要再加 SDK 空名）

| 想写的合约 | 卡在哪 | 层 |
|---|---|---|
| 两步移交 Ownable | 活网要第二把钥匙验 `accept` | 工程，不是 IR |
| 8～16 槽登记表 / 小池 | 源码展开 `xs_i` 太吵；要 IR 开 counted `for` 或宏 | **IR v0** |
| `mapping(address => uint)` | 用户 `ContractData`（Owner=用户）或 nested JSON | **存储剖面** |
| 读 XRP 余额 / Trust line | `cache_le` + `le_field`，本仓未探针 | **Runtime host** |
| swap / 真转账 | `submitTransaction` Payment / AMMDeposit | **Runtime host** |
| 日志 / 索引 | `trace_*` 未证是否共识副作用 | **探针** |
| ERC-20 façade | 永远不要 | fail closed |

依赖只能这个方向：探针绿 → Runtime 叶 → SDK `pf_inline` → Example。
没有叶子就不要门面。没有存储形状就不要 `Sdk.Map`。

## 2. 对标 EVM / SVM：学什么、抄什么会死

| EVM / SVM 已有 | XRPL 对应 | 不要抄 |
|---|---|---|
| `Access` / `Pausable` / `Roles` | **已有** Access / Pausable；Roles 可源码 2～3 个 owner 槽 | EVM Revert selector / event |
| `Storage.Vec` 连续 slot | 编译期 JSON key `xs_0`…（VEC-1） | 账户 stride / keccak |
| `Storage.Map` / `AddressMap256` | 用户 ContractData 或 nested object | RBTree / keccak(slot,key) |
| `Payments` CALL / System CPI | 宿主交易 `submitTransaction` | `call{value}` / `sol_invoke` |
| ERC-20 / SPL Token | IOU / MPToken 是账本对象 | ERC-20 字节码 |
| `ClosedCall` / CPI | 合约调合约：XRPL 还没有成熟 ABI | delegatecall / 工厂 |
| counted `for` | wasm v0 **拒绝 loop** | 假装有 Vec 迭代 |

复杂逻辑的第一道墙是 **IR v0 拒绝 loop / local / vector / map**，
不是 SDK 文件太少。

## 3. 切片（按依赖，一刀一事）

### A. 仍是组合，但要第二把钥匙 / 更大表（不新 host）

| id | 内容 | 活网怎么验 | 不做 |
|---|---|---|---|
| **wsm-018** VEC-8 | 编译期 `xs_0`…`xs_7`，仍 nested `if` | 带参，等 Parameters 502 解除；先 Bedrock | 不叫 `Storage.Vec`；不开 loop |
| **wsm-019** Roles-2 | 两个 owner 三叶 + `requireOwner` 或 | 零参数：`renounce` 变体不够；要第二种子 | 不抄 EVM `Roles.Set2` 位图 |
| **wsm-020** TwoStep | pending 三叶；`accept` 把 pending 写成 owner | 要第二把 AlphaNet 钱包 | 不新 Op |

A 解决「权限更像 Ownable2Step」，**不**解决 Uniswap。

### B. 探针（没有绿就不要 Runtime）

本 Bedrock 镜像字符串里有、本仓没接线。XLS-0102 名字可能不同；**信二进制**。

| id | host | 成功长什么样 | 失败怎么办 |
|---|---|---|---|
| **wsm-021** | `trace_num` | **已绿**（AlphaNet poke=0）。调试日志，**不开 Sdk.Log** | EVM LOG |
| **wsm-022** | `get_tx_field` 扩 sfield（fee / seq） | `XrplCtx` 多两个槽对得上 | 只留 sfAccount |
| **wsm-023** | `cache_le` | **import 已绿**；零 id → -10。还没读 Balance | 不做 `Sdk.AccountRoot` |
| **wsm-024** | nested object field | 写/读一层 JSON 对象 | 不当 Map |
| **wsm-025** | AlphaNet Parameters 502 | 公共 `submit` 带 UINT64 不再 502 | 活网继续零参数 |

探针脚本放 `runtime-tests/xrpl/probe-*.sh`，缺 Docker skip，不把 skip 当绿。

### C. 存储剖面（复杂合约的真正前置）

| id | 物理模型 | 能写的合约 | 不做 |
|---|---|---|---|
| **wsm-026** 用户 ContractData | `Owner` = 用户账户，一块 JSON | 每用户一个 UInt64 余额 | keccak map |
| **wsm-027** Amount 三叶 | XRP drops 一个 UInt64；IOU 以后 | 记「欠多少 drops」 | ERC-20 |
| **wsm-028** counted for | IR 允许编译期上界的 `for` | VEC-8 不再手写 8 个 `if` | 无界循环 / 递归 |

**wsm-026 是 Uniswap 式余额的最小前置。** 没有它，SDK 里写 `Map` 是假的。

### D. 账本效应（真动 XRP / AMM）

| id | Runtime | 能写的合约 | 不做 |
|---|---|---|---|
| **wsm-029** 读 AccountRoot.Balance | 接 wsm-023 | view 自己的 XRP | 改别人余额 |
| **wsm-030** `submitTransaction` Payment | 合约伪账户再提交 | 从合约账户付 drops | 任意 tx 类型一把梭 |
| **wsm-031** 读原生 AMM 对象 | cache_le AMM | 报价只读 | 假装是 Uniswap v2 池 |

没有 wsm-030，比赛交「链上 swap」是假的。有 wsm-026 没有 wsm-030，只能交
「内部积分账本」。

### E. 本地 AlphaNet（工程，不是语言）

| id | 内容 |
|---|---|
| **wsm-032** | 跑 `alphanet` 分支 rippled，host 表对齐 XLS-0102。**不是** Bedrock Docker |

## 4. 建议立刻做的顺序

1. **wsm-021 `trace_num` 探针** — **已绿**。不开 Sdk.Log。
2. **wsm-023 `cache_le` 探针** — **import 已绿**（零 id -10）。下一刀才是 keylet + `le_field(Balance)`。
3. **wsm-026 用户 ContractData** — 设计 + 一刀 Example：`credit` / `debit` 按 caller 分槽。
   零参数活网：`credit` 给 caller 加 1，`get` 读 caller 槽（仍是 JSON key，但 key 可以是
   固定 `"bal"` 挂在 **用户** Owner 下，不是合约 Owner）。
4. 探针绿之前 **不要** 开 `Sdk.Map` / `Sdk.Payments` / `Sdk.AccountRoot`。

比赛路径：

| 交什么 | 现在 | 还要 |
|---|---|---|
| Lean 写出、Bedrock/AlphaNet 跑通的 WASM 状态机 | **能交**（Gate/Hold/Mark） | — |
| 每用户余额的积分账本 | 不能 | wsm-026 |
| 动 XRP 的 swap | 不能 | wsm-023 + wsm-030 |
| EVM Uniswap 字节码 | 永远不要 | — |

## 5. 验收句

- 新 SDK 名必须能指出 **哪条已接线的 Runtime 叶或哪条已绿的探针**
- 存储提案必须写清：key 怎么进 ContractJson、Owner 是合约还是用户、缺字段返回什么
- 活网继续零参数，直到 wsm-025
- 不把 Bedrock Docker 当 AlphaNet；不把 skip 当绿
