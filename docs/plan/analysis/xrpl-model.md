# XRPL WASM 是什么模型（对 EVM / SVM / NEAR）

> 2026-08-29。活网事实来自本仓 AlphaNet 探针（network_id **21337**）。
> 排期仍看 [xrpl-next.md](xrpl-next.md)。本文只回答：它长什么样、为什么不像 NEAR。

## 0. 一句话

EVM 是「合约地址里有一份持久存储」。
SVM 是「程序无状态，数据在交易带来的账户字节里」。
NEAR 是「每个合约账户自带 WASM + 持久 trie 存储 + 成熟 runtime 表」。
XRPL（XLS-0101）是「账本上本来就有 AccountRoot / Trust line / AMM；WASM 是一次 `ContractCall` 里跑的脚本，经 `host_lib` 摸这些对象，用户小状态塞进 **用户自己的** `ContractData` JSON」。逻辑一份，数据按账户分片——像 SVM，但不是每人一份 wasm（见 §1.1c）。
树状结构不是「关联」就能搬：SVM 树长在程序拥有的账户字节里（见 §1.1d）。
Map / PDA / Uniswap：用户口袋有，程序金库没有（见 §1.1e）。
主账本 AMM 是 2024 起的协议对象（XLS-30），不是 WASM 写的（见 §1.1f）。
其它同类 XLS（NFT/MPT/Oracle…）清单见 [xrpl-xls.md](xrpl-xls.md)：不要用 WASM 重写。

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

### 1.1a NEAR 也有线性内存——分配器不是 Map

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
XRPL 要对齐 NEAR 集合，缺的不是分配器。变种见 §1.1b。

Lean 合约也不走 Rust `#[global_allocator]`：本仓发射 WAT 直接写死偏移，不链 wee_alloc。

### 1.1b XRPL 缺的 KV 能不能实现、变种是什么

**不能**在 wasm 里实现一个和 NEAR `storage_write` 同构的任意 key trie。
那是 runtime 给的账本能力。XRPL host 没有「任意字节 key → 任意字节 value」这条 syscall。

XLS-0101 **设计里**的持久模型是另一套，而且是一等的：

| 规范（XLS-0101） | 含义 | 像 NEAR 的哪一层 |
|---|---|---|
| 合约自己的 `ContractData` | 一块 STData/JSON，合约控制 | 顶层 `STATE`，不是 LookupMap |
| **每用户一块** `ContractData` | ID = hash(`Owner` [+ `ContractAccount`])；`setUserData(this, account, {balance})` | **按账户分片的 map**，key 是 AccountID，不是任意字符串 |
| `ContractUserDelete` | 用户删自己那块并跑 `user_delete` | 用户付 reserve、可自删 |
| `contract_info(user_account)` | RPC 读某用户那块 | view |

这是变种，不是 trie：key 空间是 **账户**，value 是那张 JSON 卡片。Uniswap 式 `mapping(address => uint)` 在规范里走这条，不走 keccak，也不走 `wee_alloc`。

**AlphaNet 今天（本仓探针）卡在实现，不卡在规范：**

| 操作 | 结果 |
|---|---|
| 写 caller 自己的卡片 | 绿（`bal=1`） |
| 写合约账户当 Owner | **-22** |
| 一次 `ContractCall` 里给 **别人** 写卡片 | 未证。规范例子是 `setUserData(this, destination, …)`；host 要接受非 caller 的 Owner |

所以间接对齐 NEAR 集合的路是：

1. **每人一张卡**（[wsm-027](../tasks/wsm-027.md) `XrplBal` 已绿）：A credit 两次=2，B credit 一次=1。多用户靠 **不同 Owner**，不是一张总表。一次调用仍不能给别人写。
2. **规范变种：user ContractData**（要对齐 NEAR `LookupMap<AccountId,_>`）：探针「合约代码给任意 AccountID 写一块」。绿了再开 Runtime 叶，SDK 才叫 `UserData.bal`，不叫 `Sdk.Map`。
3. **编译期 JSON 槽表**（VEC-1 已绿）：`xs_0`… 挂在 **同一张** caller 卡片上。小登记表，不是无界 map。
4. **nested object field**（wsm-024，未探针）：一张卡片里嵌一层对象。仍不是任意 key。
5. **不要**：wasm 堆当 map、把 AccountId 三叶拼进动态 key 字符串、抄 NEAR `storage_write` 签名到 `host_lib`。

第 2 条绿之前，不要承诺「能做 NEAR 那种 Map」。能承诺的是：规范有按用户分片；实现要 host 允许非 caller Owner。

### 1.1c 像 SVM 账户分片，不像「每人一份程序」

对：**数据和逻辑拆开**。用户的 `bal` 不在合约金库里，在 **用户自己的** `ContractData` 上（Owner=用户账户）。A credit 两次、B credit 一次，是两张卡，不是一张表里的两行。这点和 SVM「数据在用户带来的账户里」同族。

不对：**合约逻辑不是每人一份。**

| | SVM | XRPL `XrplBal` |
|---|---|---|
| 程序 | **一份** `.so`，ProgramId 全局 | **一份** wasm，一个 `ContractAccount` |
| 用户数据 | 用户（或 PDA）账户里的**原始字节** | 用户名下一块 JSON 卡片 |
| 谁付租 | 数据账户的 lamports | 卡片 Owner 的 reserve（规范；AlphaNet 未单独量） |
| 调用时带什么 | 交易必须列出要摸的账户 | `ContractCall` 只带合约 + 函数名；host 用 **caller** 当 Owner |
| 程序有没有状态 | 无（可执行账户） | 合约账户几乎也不存用户余额（写它 -22） |
| 布局 | 编译期字节偏移，程序定义、账户持有 | 编译期 JSON key，程序定义、用户持有 |

SVM 不是「每人拷贝一份 Serum」。是 Serum 这一份程序，去读写你交易里列出来的那些账户。XRPL 也不是「每人拷贝一份 XrplBal.wasm」。是那一份 wasm，每次调用时 host 自动把「当前签名者」当成数据 Owner。

所以：

- 像 SVM 的地方：逻辑一份、数据按账户分片、用户付自己那份存储。
- 不像 SVM 的地方：没有账户列表 / CPI / 原始字节布局；卡片是 JSON；一次调用默认只摸 **自己** 那张卡（给别人写还没绿）。
- 更不像 EVM：不是合约地址里一张 `mapping`。

### 1.1d 关联关系 ≠ SVM 树

「每人一张卡」是 **AccountID → 卡片** 的关联，像 SVM「每个用户一个数据账户」。
那 **不是** SVM `Sdk.Storage.RBMap` / Phoenix 订单簿那种树。

| | SVM 树 / 有序 Map | XRPL 用户卡 |
|---|---|---|
| 长在哪 | **程序拥有的账户字节**（PDA / 程序 owner） | **用户**名下的 JSON |
| 节点怎么链 | 编译期字节偏移、bump、指针在账户里 | 没有持久指针；每次 VM 扔掉线性内存 |
| 全局一本账 | 一份 orderbook 账户，程序可写 | 写合约账户 **-22**；没有程序金库树 |
| 跨用户边 | 程序同时写多个 listed 账户 | 一次调用默认只写 caller；给别人写未证 |
| 小表 | 账户内 Vec | 同一张卡上编译期 `xs_0`…（VEC-1） |

所以：

- **能做的关联**：用户 ↔ 自己的 `{bal, …}`。多用户 = 多张卡，链下或 RPC 按账户去读。不是链上遍历一棵树。
- **不能直接搬的**：程序账户里的红黑树 / 全局订单簿。那要程序可写的一块字节；AlphaNet 拒了。
- **中间态**：一张卡里几个命名槽、以后 nested JSON。仍是记录，不是无界树。

「差不太多」停在账户分片。树要程序拥有的存储，XRPL 现在没有。

### 1.1e Map 有三种；Uniswap 卡在哪一种

不必先谈红黑树。Solana 上「Map」常见是两件不同的事：

| 哪种 | Solana | XRPL 今天 | Uniswap 用哪块 |
|---|---|---|---|
| **A. 用户口袋**（PDA / 用户账户） | 每个用户（或 `seeds=[user]` 的 PDA）一块字节，程序是账户 `owner` | 每个用户一张 `ContractData` 卡片，Owner=用户。`XrplBal` 已绿 | LP 余额、个人授权 |
| **B. 程序金库**（一份全局状态） | 程序拥有的账户：池子、config、有时里面再放 Map/Vec | 写合约账户 **-22**。没有程序可写的那一块 | **储备、总 LP、手续费、pair 状态** |
| **C. 任意 key 的 KV**（`storage_write` / keccak） | 少见；或账户内手写 map | 没有。不要抄 NEAR trie / EVM mapping | 不是 Uniswap v2 的必需品 |

A 就是你说的「每个用户有他自己存东西的地方」。和 SVM PDA **同族**：逻辑一份，数据按账户分片。差别是 SVM 的 PDA 仍由 **程序** 当 `owner`（程序改字节、用户付钱）；XRPL 卡片的 Owner 是 **用户**，host 默认只让 caller 写自己的卡。

Uniswap v2 同时要 A 和 B：

```diagram
swap(caller)
  │
  ├─ 读/写 池子储备     ← B 程序金库（XRPL：写合约 -22）
  ├─ 改 caller 的 LP/余额 ← A 用户口袋（XRPL：XrplBal 绿）
  └─ 转 token             ← EVM CALL；XRPL 要 Payment / 原生 AMM
```

所以：

- **能做的**：积分、每人一份余额、每人一份配置。比赛交「Lean 写出、AlphaNet 跑通的分户状态机」可以。
- **现在做不了的 Uniswap**：共享池。没有 B，就没有「一笔 swap 改储备」。不能把池子储备写在 caller 卡片上（下一个用户看不见）。
- **XRPL 自己的出路**：主账本已经有 **原生 AMM**（下一节）。真兑换该提交 `AMMDeposit` / Payment，而不是用 WASM 重建 Uniswap 存储。EVM 侧链才是 Solidity Uniswap。
- **B 若以后绿了**（合约当 Owner，或规范里的合约自己的 `ContractData`）：才能谈程序金库 + 用户卡两边写。那仍不是 C。

担心「能不能上复杂项目」时，先问：状态是 **每人一份** 还是 **全网一份**。前者有；后者 WASM 拒了。全网一份的池子在主账本上是 **协议对象**，不是合约存储（§1.1f）。

### 1.1f 原生 AMM 不是 WASM 写出来的

之前说「按 WASM 的存储实现不了共享池」和「主账本已经有 AMM」**不矛盾**。那是两套东西：

| | Uniswap on Ethereum | XRPL 原生 AMM（XLS-30） | 用 WASM 再写一个 Uniswap |
|---|---|---|---|
| 池子存在哪 | 合约 storage | **`AMM` 账本对象** + 一个特殊 `AccountRoot` 持有资产 | 合约 `ContractData`（写合约账户 **-22**） |
| 公式谁算 | Solidity | **rippled C++**（`x*y=k`） | 我们的 wasm |
| 怎么创建 | `constructor` / factory | 交易 **`AMMCreate`** | `ContractCreate` |
| 怎么加池 / 换 | 合约函数 | **`AMMDeposit` / `AMMWithdraw` / `Payment`** | `ContractCall` |
| 每交易对几个池 | 任意多个合约 | **协议层最多一个**（流动性不碎片化） | 若能写金库，仍是我们自己的碎片 |
| 主网 | 多年 | **2024-03 amendment 已开** | `ContractCreate` **还没有** |

XLS-30 自己写：AMM 是 **protocol native**，开发者 **不必** 为了兑换去写智能合约。储备在特殊账户的 Balance / trust line 上，不在 WASM JSON 里。任何人发 `AMMCreate`，共识按 C++ 规则改那个 `AMM` 对象——和 Payment 改 AccountRoot 是同一类机制。

所以：

- 「实现不了」指的是：**用我们这套 WASM 卡片，仿不出 Uniswap 那种合约金库。**
- 「主账本已经有」指的是：**兑换功能 2024 起就是账本交易，跟 WASM 无关。** 不经过 `host_lib`，也不需要程序可写的 `ContractData`。
- WASM 以后若要「用」这个 AMM：`cache_le` 读 `AMM` 对象（只读）+ `submitTransaction` 发 `AMMDeposit`。那是 **调用** 原生对象，不是 **实现** 一个池子。
- 想自写曲线 / Uniswap v3 式合约：要么等 WASM 能写程序金库，要么走 **EVM 侧链**。主账本不会因为有了 WASM 就把 XLS-30 拆掉重写成合约。

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
