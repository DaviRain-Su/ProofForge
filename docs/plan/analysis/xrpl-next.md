# XRPL 下一阶段：复杂合约还差什么

> 2026-08-29。HEAD 本切片（wsm-038）之后。本文是 **wsm-018+** 的排期，
> 接 [xrpl-sdk-gap.md](xrpl-sdk-gap.md) / [xrpl-runtime.md](xrpl-runtime.md)。
> 学 EVM/SVM 的分层，不学 keccak slot / account bytes / CPI。
>
> **XLS-0101/0102 底层没完。** 已绿：emit/assemble、两套 host 表、用户卡片、
> env 叶、`callerBalanceDrops`、AccountRoot Sequence/Flags/OwnerCount。
> 发交易 host **已注册**（`build_txn` pokeBuild=0）。公开 3.3.0 **注资已绿**
> （新 hash 第一次 Create 两数组 `tfSendAmount`）。`emit_built_txn` Payment 仍
> **-196 tefBAD_AUTH**（不是没钱；`tecPSEUDO_ACCOUNT` 是 +196）。
> 给别人写卡片 **已绿**（`set_data_object_field` 填对方 20B，不是 `setUserData` 名）。
> 还缺：程序拥有 ContractData（-22）、emit -196 tefBAD_AUTH。
> 公开 Parameters **已绿**。`increment(1)`、`initialize(7)`、`XrplVec.setAt(1,5)`、
> `XrplNest` A `credit(3)` / B `credit(5)`（nested `{user:{bal}}`）、`XrplBal` A `credit(3)` / B `credit(5)`、
> `XrplTab.setAt(3,7)`（`xs_3=7`）、`XrplSend.credit(w0,w1,w2,7)`、`XrplPay` 积分转账、`XrplMint` A `mint(5)` / B `mint` 拒 / A `pay(B,2)` → A=3 B=2 都绿。
> emit 官方 Amount+Destination 仍 **-196 tefBAD_AUTH**（`checkSign` 伪账户检查在
> inner-batch 旁路之前；`fixCleanup3_3_0` + `LendingProtocol` 已开）。合约卡 **-22**。
> 新的 `tfSendAmount` Create 现为 **temBAD_SIGNATURE**（节点 sign 也拒）。
> **不要开 `Sdk.Amm` / `Sdk.Payments` / `Sdk.Nft`。**

## 0. 现在能写什么样的合约

活网（AlphaNet 21337，零参数）已经能组合：

| 合约 | 能力 |
|---|---|
| `XrplSmoke` | 无权限 Counter |
| `XrplGate` | Ownable + `renounce`（状态码 3） |
| `XrplHold` | Ownable + Pausable（状态码 4） |
| `XrplMark` | owner 门后写 SHA-512Half 字面量 |
| `XrplVec` | 编译期 3 槽表（Bedrock 本地；活网带参 502） |
| `XrplStep` | TwoStep Ownable（`propose` / `accept`）；活网同钱包自提名 |
| `XrplRole` | owner + operator；`setOp` 后 `requireOwnerOr` |
| `XrplPeer` | 编译期 AccountID 的 XRP Balance（drops）；persist 仍是 caller |
| `XrplFlag` | ContractCall Flags |
| `XrplTab` | 4 槽 `xs_0`…`xs_3`；活网 `setAt(3,7)` → `xs_3=7`，`sum4`=7 |
| `XrplHand` | 跨钱包 TwoStep：第二把钥匙部署到创世卡片，创世 `accept` |
| `XrplCrew` | 跨钱包 operator：第二把钥匙 owner，创世 `setOp` 后 `bump` |

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
| 读 XRP 余额 / Trust line | `cache_le` + `le_field` | **已绿** Balance；Trust line 未探针 |
| swap / 真转账 | `build_txn` / `emit_built_txn` Payment（**不是**叙事名 `submitTransaction`） | **Runtime host** |
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
| `Payments` CALL / System CPI | 宿主交易 `build_txn` + `emit_built_txn` | `call{value}` / `sol_invoke` |
| ERC-20 / SPL Token | IOU / MPToken 是账本对象 | ERC-20 字节码 |
| `ClosedCall` / CPI | 合约调合约：XRPL 还没有成熟 ABI | delegatecall / 工厂 |
| counted `for` | wasm v0 **拒绝 loop** | 假装有 Vec 迭代 |

复杂逻辑的第一道墙是 **IR v0 拒绝 loop / local / vector / map**，
不是 SDK 文件太少。

## 1.1 不要做 wasm 分配器当 SDK 底座

XLS-0102 §4 / §6.3：每次执行 **新建 VM**；线性内存一次调用内有效，**不跨 `ContractCall`**。
本仓 WAT 已经是 `(memory (export "memory") 1)`（64KiB），偏移钉死：

| 偏移 | 用途 |
|---|---|
| 0..19 | 存储 Owner AccountID |
| 20..27 | `function_param` scratch |
| 28..36 | UINT64 编解码 |
| 64+ | 槽名 ASCII |

SVM `BumpAllocator` 活在 **账户字节里的持久 heap**。XRPL 持久状态是
`ContractData.ContractJson`，经 host 进出，不经 wasm 堆。

所以：

- **能做**：调用内固定 scratch（host 缓冲、编解码）。发射器已经在做，不必再造 malloc。
- **不要做**：把 bump allocator 当 `Sdk.Map` / Vec 的底座。跨交易的余额必须换
  **存储 Owner**（用户 ContractData）或 nested JSON，不是 `memory.grow`。
- 有了分配器 **不能** 就「上层造 SDK」。缺的是账本形状，不是堆。
  NEAR 默认分配器是 `wee_alloc`（调用内）；`LookupMap` 走 `env.storage_write`。
  详见 [xrpl-model.md](xrpl-model.md) §1.1a / §1.1b。

## 2. 切片（按依赖，一刀一事）

### A. 仍是组合，但要第二把钥匙 / 更大表（不新 host）

| id | 内容 | 活网怎么验 | 不做 |
|---|---|---|---|
| **wsm-018** VEC-8 | 编译期 `xs_0`…`xs_7`，仍 nested `if` | 带参，等 Parameters 502 解除；先 Bedrock | 不叫 `Storage.Vec`；不开 loop |
| **wsm-019** Roles-2 | **已绿**（`XrplRole`）。同钱包 `setOp` 自指 operator | 第二把钥匙才能证「非 owner 的 operator」 | 不抄 EVM `Roles.Set2` 位图 |
| **wsm-020** TwoStep | **已绿**（`XrplStep`）。同钱包 `propose`+`accept` | 第二把钥匙才能证跨账户移交 | 不新 Op |

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
| **wsm-026** 用户 ContractData | 公开 **blocked -22**；本地 2.6.1 **注资后绿**（合约卡 `bal=1`）。单用户 `"bal"` 公开就能做 | 公开程序卡要等注资 Create | keccak / wasm heap |
| **wsm-027** Amount 三叶 | XRP drops 一个 UInt64；IOU 以后 | 记「欠多少 drops」 | ERC-20 |
| **wsm-028** counted for | IR 允许编译期上界的 `for` | VEC-8 不再手写 8 个 `if` | 无界循环 / 递归 |

**wsm-026 是 Uniswap 式余额的最小前置。** 没有它，SDK 里写 `Map` 是假的。

### D. 账本效应（真动 XRP / AMM）

| id | Runtime | 能写的合约 | 不做 |
|---|---|---|---|
| **wsm-029** 读 AccountRoot.Balance | **探针绿**；Runtime 解码叶下一刀 | view 自己的 XRP | 改别人余额 |
| **wsm-030** `build_txn` / `emit_built_txn` Payment | **host 已绿**（pokeBuild=0）。pokeEmit **-196** `tecPSEUDO_ACCOUNT`；普通 Payment 打合约 = `tecNO_PERMISSION`。叙事名 `submitTransaction` 不是 import | 从合约账户付 drops | 任意 tx 类型一把梭；不开 `Sdk.Payments` 直到 pokeEmit tesSUCCESS |
| **wsm-031** 读原生 AMM 对象 | cache_le AMM | 报价只读 | 假装是 Uniswap v2 池 |

没有 wsm-030，比赛交「链上 swap」是假的。有 wsm-026 没有 wsm-030，只能交
「内部积分账本」。

### E. 本地 AlphaNet（工程，不是语言）

| id | 内容 |
|---|---|
| **wsm-032** | **已跑** `transia/alphanet:latest` = 2.6.1-rc1 `dangell/smart-contracts` @ `56f16869`，nid **63456**。**不是** Bedrock Docker，也 **不是** 公开 3.3.0 / XLS-0102 名。host 是 `get_*`。本地 **emit Payment 绿**（values-only `tfSendAmount` + 大端 NetworkID）。公开 3.3.0 仍 -196 / temMALFORMED。合约账户卡仍 **-1**；Parameters **SIGSEGV** |

## 3. 建议立刻做的顺序

1. **wsm-021 `trace_num` 探针** — **已绿**。不开 Sdk.Log。
2. **wsm-029 / wsm-033** — AccountRoot.Balance **已绿**（`callerBalanceDrops`）。
3. **wsm-030 / wsm-032** — 本地 2.6.1 **Payment 已落地**。公开 3.3.0
   **注资已绿**（新 hash 第一次 Create 两数组 `tfSendAmount`）。`pokeEmit` 仍
   **-196 tefBAD_AUTH**（伪账户签名预检；不是没钱）。不开 `Sdk.Payments`。
4. **wsm-034** — AccountRoot Sequence/Flags/OwnerCount **已绿**（`XrplRoot`）。
5. **wsm-027 XrplBal** — **已绿**：每人一张卡（A `credit(3)`=3 / B `credit(5)`=5）。
6. **wsm-035** — 给别人写卡片 **已绿**（硬编码对方 AccountID）。`tx Sequence/Fee` 已绿。
   `amm_id` host 在（零 issue -15）。不开 Sdk.Map / Sdk.Amm。
7. **wsm-036** — `Context.storeOwnerLimbs w0 w1 w2` 覆盖存储 Owner。`XrplSend.credit(w0,w1,w2,amount)` 写第二把钥匙的卡片。
8. **wsm-037** — nested JSON `user_bal` → `{user:{bal}}`（AlphaNet）。`credit(delta)` 一个 UINT64。双钱包 A=3 / B=5。不是 Map。
9. **wsm-038** — TwoStep / dual role / `litBalanceDrops` / `txFlags` **已绿**。
10. **wsm-039** — `forAccum` 编译期展开 + 跨钱包 TwoStep（`XrplHand`）**已绿**。运行时下标仍拒。
11. **wsm-040** — 跨钱包 operator（`XrplCrew`）**已绿**。
12. **XrplPay** — 内部积分转账：先 peek dest，再切回 caller `flushBal`。余额不足不扣款。不是 XRP Payment。
13. **XrplMint** — 编译期 minter 才能 mint / `mintTo`；任何人可 `burn`；`halt` / `supp` 在 minter 卡上；暂停后 mint/pay/`mintTo`/`burn` 状态码 4。`supp` 随 mint/mintTo 增、burn 减，pay 不变。
14. **不要** wasm bump allocator 当 SDK 底座（§1.1）。**不要** `Sdk.Map`。

比赛路径：

| 交什么 | 现在 | 还要 |
|---|---|---|
| Lean 写出、Bedrock/AlphaNet 跑通的 WASM 状态机 | **能交**（Gate/Hold/Mark） | — |
| 每用户余额的积分账本 | 公开只能 caller 卡；本地注资后程序卡已绿 | 公开 tfSendAmount |
| 动 XRP 的 swap | 不能 | wsm-023 + wsm-030 |
| EVM Uniswap 字节码 | 永远不要 | — |

## 3.1 v0 能做完的已经做完

本仓能接线的 Runtime / SDK 组合层（零参数、JSON 槽、三叶 AccountId、读 AccountRoot / tx_field、写别人卡片、nested JSON）到 wsm-038 收口。

**节点挡住、本仓做不完：**

| 缺口 | 现场 |
|---|---|
| 伪账户注资 / 发出 Payment | `emit_built_txn` = -196；Create `InstanceParameters` temMALFORMED；Payment 打合约 tecNO_PERMISSION |
| 公共 ContractCall Parameters | HTTP 502 |
| 程序拥有 ContractData | set 合约账户 = -22 |
| Sdk.Amm / Sdk.Payments / Sdk.Map / Sdk.Nft | 上面三条没绿之前不开 |

不要把 XRPL v0 说成「做完」。节点修之前，再切 SDK 也只是同一套叶子换名字。

## 4. 验收句

- 新 SDK 名必须能指出 **哪条已接线的 Runtime 叶或哪条已绿的探针**
- 存储提案必须写清：key 怎么进 ContractJson、Owner 是合约还是用户、缺字段返回什么
- 活网继续零参数，直到 wsm-025
- 不把 Bedrock Docker 当 AlphaNet；不把 skip 当绿
