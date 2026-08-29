# XRPL Runtime：向 EVM / SVM 学什么

> 2026-08-29。wsm-003 本地 Counter 四场景已绿。本文是 XRPL Runtime
> 的权威排期，对标 [05-evm-coverage-slices.md](../../research/05-evm-coverage-slices.md)
> 的 E-RT 切法和 [runtime-sdk-roadmap.md](../runtime-sdk-roadmap.md) 的
> Runtime-先于-SDK。NEAR [PR #5](https://github.com/DaviRain-Su/ProofForge/pull/5)
> 停在同一层（host 表 + 存储，无 Runtime 叶子）；两条链各自拥有叶子，
> 不共享 Plan / digest / import 表。

## 1. 现在停在哪

| 层 | XRPL 现状 | EVM / SVM 对照 |
|---|---|---|
| 产物 | Lean → WAT → `.wasm`，锁定 `wat2wasm` | Yul/`solc`，`.s`/`sbpf` |
| Host 表 | `host_lib`：`function_param`、`get_current_ledger_obj_field`、`get/set_data_object_field` | opcode / syscall |
| 存储 | 发射器把 `State` 槽写成 `ContractData.ContractJson` | EVM slot / SVM account bytes |
| Runtime 叶子 | caller/self/ledger/hash 字面量已绿 | `Evm.Runtime.evmCaller`、`Svm.Runtime.clockSlot` |
| SDK | `Context` / `AccountId.eq` / `Hash`；缺口见 [xrpl-sdk-gap.md](xrpl-sdk-gap.md) | `Evm.Sdk.caller`、`Svm.Sdk.Account` |
| 工程门 | `counter.sh` / `ctx.sh` / `own.sh` / `hash.sh` | Anvil / Mollusk |

合约还不能写「读 caller / 账本序号」。存储是发射器偷偷调 host，源码看不见宿主。

## 2. 向谁学、不学什么

学 EVM/SVM 的**分层和抽出规矩**，不学它们的物理模型。

```diagram
┌────────────────────────────────────────────┐
│ 普通 Lean · @[pf_entry] · Extract · Core CFG │
└─────────────────────┬──────────────────────┘
                      ▼
┌────────────────────────────────────────────┐
│ Extract.IR.ValKind = svm | evm | xrpl | …  │
│ Decode 认 ``ProofForge.Wasm.Xrpl.Runtime.*``│
└─────────────────────┬──────────────────────┘
                      ▼
┌────────────────────────────────────────────┐
│ Xrpl.Ops / IR / Emit                       │
│ 叶子 → host_lib 调用（本链 import 表）       │
└─────────────────────┬──────────────────────┘
                      ▼
┌────────────────────────────────────────────┐
│ Xrpl.Sdk（后做）                            │
│ pf_inline，只组合已有 Runtime，不新增 Ops    │
└────────────────────────────────────────────┘
```

| 学 | 不学 |
|---|---|
| `@[irreducible]` stub，抽出按**全名**认 | 把 `clockSlot` 当成账本序号 |
| 结构体拆成 UInt64 叶（Addr20 → AccountId） | 复用 `Evm.Runtime.Addr20` 类型 |
| SVM/EVM/XRPL/NEAR 叶子互拒 | 通用 wasmtime / `pf` import |
| Runtime 先于 SDK | 第一刀就做 Ownable / Map |
| 验收按合约能力 + 本地节点 | 主网 `deployable` |

NEAR 现在同样没有 Runtime（[PR #5](https://github.com/DaviRain-Su/ProofForge/pull/5) 的 `wsm-004` 是 `env` 表 + sandbox Counter）。它的下一刀应是 `Near.Runtime.predecessor`，走 `env.predecessor_account_id`，**不是** XRPL 的 `get_tx_field`。Extract 加 `.xrpl` 之后，NEAR 加 `.near` 抄同一模式，不要合进一个 `.wasm` 构造子。

## 3. 共享锁：Extract.IR 必须开第三条臂

抽出器今天只认识：

```lean
inductive ValKind where
  | svm (kind : Svm.Ops.ValKind)
  | evm (kind : Evm.Ops.ValKind)
```

XRPL 叶子不能塞进 `.evm`。第一刀要：

1. `Extract.IR.ValKind` / `OpExt` 加 `| xrpl …`
2. `Extract/Decode.lean` 认 `ProofForge.Wasm.Xrpl.Runtime.*`
3. `Svm.IR` / `Evm.IR` 投影拒绝 `.xrpl`
4. `Wasm.Family.rejectValKind` 继续拒 svm/evm；NEAR 以后拒 `.xrpl`

这是和 NEAR 的**共享写集**。XRPL 先加 `.xrpl`；NEAR Runtime 另开 `.near`，不要抢这一刀。

## 4. 身份：AccountId，钉死三叶

XRPL `AccountID` 是 20 字节，和 EVM address 同宽、**不是**同一种值。

```lean
structure AccountId where
  w0 : UInt64   -- bytes 0..7  little-endian
  w1 : UInt64   -- bytes 8..15
  w2 : UInt64   -- bytes 16..19 in the low 4 bytes
```

和 `Addr20` 同形，但是 `ProofForge.Wasm.Xrpl.Runtime.AccountId`。比较、当存储槽、当 `get_tx_field` 目标都走这三叶。废弃「只返回低 8 字节当身份」。

## 5. 本 Bedrock 镜像已经有的 host（第一刀只用这些）

在 `lejamon/rippled_smart_contract_vault_x86` 的 `rippled` 里确认过：

| host | 签名 | 第一刀 |
|---|---|---|
| `get_tx_field` | `(i32 field, i32 ptr, i32 len) → i32` | `sfAccount=524289` → caller 20B |
| `get_current_ledger_obj_field` | 已用 | `sfContractAccount=524315` → self 20B |
| `get_ledger_sqn` | `() → i32` | 当前账本序号，零扩展到 UInt64 |
| `get_parent_ledger_time` | `() → i32` | parent close time，零扩展 |
| `function_param` / `set_data_object_field` | 已用 | 不改 |

负返回码沿用现有 `missingFields`。`get_parent_ledger_hash`、`get_base_fee`、`compute_sha512_half`、`trace` 第二刀再开。

## 6. 切片（验收按合约能力）

依赖只能这个方向。没有 AccountId 就不要做 Ownable。没有环境叶就不要做 SDK。

### XRPL-RT（[wsm-005](../tasks/wsm-005.md)）— 下一刀

一次交付，不拆叶：

| Lean | host |
|---|---|
| `xrplCallerW0/W1/W2`、`xrplCaller20` | `get_tx_field(sfAccount)` |
| `xrplSelfW0/W1/W2`、`xrplSelf20` | `get_current_ledger_obj_field(sfContractAccount)` |
| `xrplLedgerSqn` | `get_ledger_sqn` |
| `xrplParentTime` | `get_parent_ledger_time` |

`Examples.XrplCtx`：view 返回序号；mutate 把 caller 低 8 字节和序号写进 `State` 槽。本地节点：`ContractCall` 后 `ContractJson` 对上 genesis 账户 / 账本序号。SVM/EVM 拒全部新叶。digest 域仍 `xrpl-bedrock|`。

不做：hash、event、Map、SDK、主网、NEAR 叶子。

### XRPL-CMP（[wsm-006](../tasks/wsm-006.md)）

源码嵌套 `if caller.w0/w1/w2 = owner0/1/2`。不新增 host。`errorNamed "unauthorized"`
钉死 wasm `i32` 状态码 **3**。`Examples.XrplOwn`：genesis `init`+`bump` 改 `value`；
第二账户 `bump` 返回 3 且槽不变。

### XRPL-HASH（[wsm-007](../tasks/wsm-007.md)）

本镜像确认了 `host_lib.compute_sha512_half`（不是 stdlib 的 `sha512_half`）。
`xrplSha512HalfLit "vault"` 对标 `sha256Lit`：ASCII 字面量 → SHA-512Half 首个小端
UInt64。完整 32B / 动态输入 / keccak 仍 FC。`Examples.XrplHash` 把结果写入槽。

### XRPL-SDK（[wsm-008](../tasks/wsm-008.md)）

`Xrpl.Sdk.Context.caller / self / ledgerSqn`，全部 `@[pf_inline]` 转到 Runtime。
`AccountId.eq` 也是 `@[pf_inline]`，展开成三叶嵌套 `if`（[wsm-009](../tasks/wsm-009.md)）。
Ownable 走这个 helper，不是新 Op。8 字节 `callerLo` 只是截断视图。

后续 SDK / Runtime 缺口（Vec、Map、日志、第二批 host）见
[xrpl-sdk-gap.md](xrpl-sdk-gap.md)。复杂合约下一阶段（用户 ContractData、
`cache_le`、`submitTransaction`）见 [xrpl-next.md](xrpl-next.md)。
官方 Rust crate 对照见 [xrpl-rust-sdk.md](xrpl-rust-sdk.md)。
不要把 SVM RBMap 或 EVM hashed Map 接到 XRPL。

## 7. 明确 fail closed

- `clockSlot` / `evmCaller` / NEAR `predecessor` 出现在 XRPL 模块
- 8 字节身份当转账或权限目标
- `update_data` 当持久化（本镜像不落账本）
- 把 view `i64` 当成 `meta.ReturnValue`（本宿主不填；状态读 `ContractJson`）
- 通用 `.wasm` ValKind 把 XRPL 和 NEAR 叶子混在一起

## 8. 和 NEAR 怎么错开

| | XRPL（本分支） | NEAR（PR #5 / `wasm-near`） |
|---|---|---|
| 已绿 | WAT + Bedrock 四场景 | WAT + sandbox 四场景 |
| Runtime | **本刀** `wsm-005` | 等 `.xrpl` 进 Extract 后再加 `.near` |
| 第一批叶子 | caller / self / ledger sqn / parent time | predecessor / current_account / block_timestamp |
| host 模块 | `host_lib` | `env` |
| 任务号 | `wsm-005+` | 他们已用 `wsm-004`；Runtime 建议 `wsm-near-rt-001` |

不要在 XRPL 分支改 `ProofForge/Wasm/Near/**`。Extract.IR 的 `.xrpl` 构造子是唯一共享文件；合入后通知 NEAR 线抄模式加 `.near`。
