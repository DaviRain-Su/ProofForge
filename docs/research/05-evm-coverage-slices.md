# EVM 覆盖：还差什么，按大切片切

> Date: 2026-08-22
> Core question: 相对 ProofForge 已落地的 EVM 工程面，以及一份「能写真实合约」的最小 EVM 剖面，本仓还缺什么？怎样用少数大切片做完，而不是继续一叶一叶加？
> Related: [04-evm-feasibility.md](04-evm-feasibility.md) · PF [01-evm.md](file:///Users/davirian/orca/projects/proof_forge/docs/targets/01-evm.md)

---

## 一、先下判断

**现在不是「通用 EVM 合约编译器」。** 管子通了：普通 Lean → 抽出 → Yul → solc → Anvil。语言面和 runtime 面都还是白板。

对照有两把尺，不要混：

| 尺 | 含义 | 本仓要不要追平 |
|---|---|---|
| **A. 本仓诚实剖面** | 普通 Lean 子集能写、能证、能在 Anvil 上跑的单合约 | **要。这是产品** |
| **B. PF EVM 工程面** | `SemanticProgramV1` + capability + Map/Field/Principal/assets/crypto | **不要整包搬。按需摘形状，不摘 DSL / Semantic / 1 万行 Lower** |

「完全覆盖 EVM feature」若按 B，那是多年 PF 工作量，且 PF 自己也没闭合 formal / 主网 / 动态 callee。本仓的「覆盖完」应钉成 **A 的天花板**：单合约、定宽状态、封闭效应、fail-closed。

下面按 A 列缺口，并标出 B 里哪些形状值得抄、哪些明确不做。

---

## 二、本仓现在有（量化）

抽出 / Ops 一共这些：

- `Val`：`arg` / `field` / `lit` + SVM 三叶 + EVM 两叶（`evmCaller` 低 8B、`evmBlockNumber`）
- `Op`：checked 四则、`ite`、`systemTransfer`、`okState` / `return*`
- 叶子类型：`UInt8/16/32/64`、`Option UInt64`、定长 `Vector UInt64 n`、无 payload 枚举
- Anvil：Counter / Pair / Flag / Maybe / EvmCtx（Darwin+Linux）

明确拒绝：`clockSlot` / `signerKey0` / `systemTransfer` 进 EVM；EVM 叶子进 sBPF。这是对的，不要改。

---

## 三、对照 PF EVM：按面，不按文件

PF `Targets/Evm` ≈ 1.1 万行。能抄的是 **Yul 形状和 Anvil 矩阵**，不是 `planFromCapability`。

### 已对齐（形状级）

| 面 | PF | 本仓 |
|---|---|---|
| constructor + selector dispatch | 有 | 有 |
| checked `+ - * / %` + revert 不提交 | 有 | 有 |
| `ite` | 有 | 有 |
| `UInt8/16/32/64` storage word | 有（窄 mask） | 有 |
| `Option UInt64` 双槽 | 有 | 有 |
| `number()` | `context.blockHeight` | `evmBlockNumber` |
| `CALLER` 某种形式 | 完整 20B Principal 九叶 | 低 8 字节 `evmCaller` |

### 未对齐、且属于尺 A（要做）

| 面 | PF 已有 | 本仓 | 为什么算「覆盖完」必需 |
|---|---|---|---|
| 环境读完整集 | `timestamp` / `chainid` / `callvalue` / `selfbalance` / `address()` | 无 | 真实合约几乎都要时间、链、自己 |
| caller 身份 | 20 字节 `u32le(20)\|\|addr20` | 只 8 字节 | 8 字节不能当地址用，也不能做 Ownable |
| payable / ETH 进出 | `deposit` = `eq(callvalue(),amt)`；`transfer` = value CALL | 无 | 没有 value 就没有 tip / vault |
| event | `emit` → LOG | 无 | 链下索引的标准面 |
| 命名错误 | `revert` + selector | 只有 `revert(0,0)` | overflow 以外的业务错误 |
| 位运算 / 移位 | `and/or/xor/not/shl/shr` | 无 | Flag / 权限位 / packed 字段 |
| 有界循环 | `for i < N` | 无 | 定长 Vector 批量、简单结算 |
| 定长数组下标 | `indexGet/Set` + bounds revert | Vector 只展开成具名槽 | `window[i]` 不能写 |
| hashed Map | `Map k v` 一 base slot | 无 | 余额表 / 授权表 |
| 封闭 ERC-20 | `token.transfer` + `balanceOfSelf` | 无 | 否则永远写不成 Token 合约 |
| ABI 不止 `uint64` | 窄/宽/tuple | 入口参数全是 `uint64` | `setFlag(uint8)` 现在是假的 |
| 多叶 return | tuple | 只 return 一个 `uint64` | `getBoth` 编不出来 |

### 未对齐、属于尺 B（明确不做，不是延期）

- `program … where` / SemanticProgram / capability / 167k 闭包
- Field(bn254) / UInt128/256 当默认算术（EVM word 可以后开，不当 v0 必达）
- 有符号 Int 全家
- 动态 callee、delegatecall、create2、proxy
- Token-2022、主网、`.bin` refinement
- 把 `systemTransfer` 译成 ETH transfer
- 无界循环、`IO`、一般递归

PF 自己也 FC：Map 作参数、嵌套 Option、真实 deployment-address binding、formal Anvil differential。

---

## 四、三块大切片（建议就这三刀）

目标：三刀之后，能写 **Ownable 计数器 + ETH tip jar + 简单 ERC-20 金库**，并且每刀都有 Anvil 矩阵，不再拆成「先 timestamp、再 chainid」。

```diagram
┌─────────────────────────────────────────────┐
│ E-RT  环境 + value + 身份                    │
│ timestamp / chainid / self / callvalue      │
│ caller 20B / payable / ETH transfer / event │
└──────────────────┬──────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────┐
│ E-LANG  语言面（仍单合约）                    │
│ 位运算 · 有界 for · Vector[i]                │
│ 窄 ABI · 多叶 return · 命名 revert           │
└──────────────────┬──────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────┐
│ E-ASSET  状态表 + 封闭 token                 │
│ Map UInt64/address → UInt64 (hashed)        │
│ ERC-20 transfer + balanceOfSelf             │
└─────────────────────────────────────────────┘
```

依赖只能是这个方向。E-ASSET 没有 20B caller 和 payable 会写成谎言。E-LANG 可以和 E-RT 后半并行，但 **不要** 在 E-RT 没绿时开 Map。

### 切片 E-RT：环境、value、身份

**一次交付，不要拆成五条任务。**

Lean 新名（全是独立 EVM 叶，SVM 发射器一律拒）：

| 名 | Yul | 约束 |
|---|---|---|
| `evmTimestamp` | `timestamp()` | `> 2^64-1` revert |
| `evmChainId` | `chainid()` | 同上 |
| `evmSelf` | `and(address(), 2^64-1)` | 与 caller 同宽策略，见下 |
| `evmCallValue` | `callvalue()` | 读到它的 entry 变 payable；view 仍 0 |
| `evmSelfBalance` | `selfbalance()` | 超 UInt64 revert |
| `evmCaller20` / `evmSelf20` | 20 字节 | **替换** 或并列于当前 8 字节叶 |

**20 字节身份（本仓简化，不搬 PF 九叶 Principal）：**

两个选择，切片里必须钉死一个：

1. **推荐**：`structure Addr20 where w0 w1 w2 : UInt64`（w2 只低 4 字节）。storage 三槽。比较、当 CALL 目标都走这三叶。废弃「只返回低 8 字节当身份」。
2. 继续 8 字节：永远做不了转账目标。只当调试叶留下。

效应（封闭，编译期钉死）：

| 名 | 语义 |
|---|---|
| `evmDeposit (amt)` | `eq(callvalue(), amt)`，否则 revert；无 storage 变化 |
| `evmSendEth (dst : Addr20) (amt)` | `call(gas(), addr, amt, 0,0,0,0)`，失败 revert。**重入诚实**：Reference 无重入，文档写死 |
| `evmEmit (name) (args…)` | LOG；topic = keccak(签名)；data = 32B 字 |

Anvil 矩阵（一条脚本，多段）：timestamp 单调；chainid=31338；deposit 精确 value；错 value revert 且 storage 保持；sendEth 改余额；emit 能被 `cast receipt` 看到；caller20 对上 `cast wallet address`。

不做：`tx.origin`、`blockhash`、`gasleft`、`basefee`、create/create2。

### 切片 E-LANG：还像编译器

一次交付：

1. **位运算**：`&&& ||| ^^^ ~~~ <<< >>>` 抽成 Op；移位 count≥64 或结果超宽 revert。
2. **有界 `for`**：只接受 `for i in [0:N]`，`N` 编译期常量（先 ≤64）。超次 revert。
3. **`Vector.get / set` 运行时下标**：`i` 是 `Val` 不是字面量；`i ≥ n` revert。现在只展开具名槽，这一刀才叫数组。
4. **ABI**：参数/返回按槽宽声明 `uint8/16/32/64`。`setFlag(uint64)` 改成 `uint8` 或继续 uint64 但文档诚实——**推荐改真 ABI**。
5. **多叶 return**：`getBoth` → `(uint64,uint64)` tuple。`returnState` 多槽已经会写；缺的是 ABI 出口。
6. **命名 revert**：`inductive Error` 的非 overflow 构造子 → `revert(0,0)` 仍可，但 selector 用 `keccak("ErrorName()")` 前 4 字节，方便 Anvil 对 `cast` 错误名。

Anvil：位运算夹具、`for` 求和、`window[i]` 越界、tuple return、命名 revert。

不做：一般递归、`while`、动态 `Array`、嵌套 Option。

### 切片 E-ASSET：能写金库

一次交付：

1. **`Map UInt64 UInt64`**：一 base slot；`keccak256(key || base)` → occ + payload（抄 PF hashed helper 形状，不抄 24/44 叶 dense）。
2. **`Map Addr20 UInt64`**：key 三叶进 memory 再 keccak。这是余额表。
3. **封闭 ERC-20**：
   - `evmTokenTransfer (token dst amt)`：callee = token 的 20B；calldata `0xa9059cbb` + addr + amt；returndatasize 0 或 32 非零。
   - `evmTokenBalanceOfSelf (token)`：`STATICCALL balanceOf(address(this))`。

Anvil：需要一个最小 ERC-20 mock（可手写 30 行 Yul/Solidity 夹具，钉在 testdata，不引进 Foundry 工程）。转 1000、超额 revert 状态保持、USDT 无返回成功。

不做（本刀）：approve/allowance（第四刀 E-OWN）、Token-2022、任意 CALLEE。

---

## 五、三刀之后「覆盖完」长什么样

能写、能 Anvil 的合约：

- Ownable：`owner : Addr20`，`require caller20 = owner`
- TipJar：`deposit` + `sendEth`
- 计数器 + event `Incremented(uint64)`
- 金库：收 ERC-20，按 `Map Addr20 UInt64` 记份额

第四刀 **E-OWN**（本仓继续）：Ownable 三槽 + 通用 `LOG Name(uint64)` + pair-key allowance / spend。

仍不能写：DEX 全套、NFT、代理升级、跨合约任意调用、主网部署声明。那不是「再开几个切片」，是另一条产品线。

---

## 六、和「一点一点做」怎么切开

| 旧做法 | 大切片 |
|---|---|
| evm-008 只加 number | E-RT 一次加完环境+value+20B+event |
| 下一个再加 timestamp | 同一 Anvil 脚本里断言 |
| Map 单独开、token 再开 | E-ASSET 一次：hashed map + 一条 ERC-20 |

每刀仍要：Runtime 名 + Extract + Evm.Emit + 一个 Examples + 一条 Anvil。只是 **验收按合约能力**，不按「又多了一个 opcode」。

预估（量级，不是承诺）：

| 切片 | 相对已做的 E0–E8 | 风险 |
|---|---|---|
| E-RT | 约 2–3 个现有刀的体量 | Addr20 布局一旦写进 storage 就难改 |
| E-LANG | 约 2 刀 | 运行时下标会逼 Extract 改最大 |
| E-ASSET | 约 3 刀 | keccak helper + ERC-20 mock；重入必须写进文档 |

---

## 七、建议的下一步

1. **先钉 E-RT 的 Addr20 选择**（上面推荐三 `UInt64` 叶）。错了后面 Map/转账全要返工。
2. 开 E-RT，不要先开 Map。
3. Window / Phase / Choice 的 Anvil **不进这三刀**（你已否 Window；Phase/Choice 是发射器回归，不是覆盖）。

用户拍板 Addr20 方案后，下一回合按 E-RT 整包做，不再拆叶。
