# 补全依据：对谁对齐

核心问题：本仓相对 ProofForge「不全」，该按什么补？要不要按官方 Solana Program SDK（Rust）做规划？

结论先说：

1. **不要**按 ProofForge 的工程清单补全。那是别人选过的封闭 recipe，不是 Solana 的天花板。
2. **要看官方**，但看的是 **Program 运行时契约 + sBPF syscall 表**，不是把 `solana-program` crate 当待实现 API。
3. `solana-program` 是 Rust 对那份契约的编码，而且混了链下符号。官方自己也说：Rust 上链是受限子集。本仓对 Lean 做同样的事。

## 三层权威

```diagram
┌─────────────────────────────────────────────┐
│ 1. SVM / Loader / syscall（官方天花板）      │
│    账户五元组、entrypoint、CPI 特权延伸、     │
│    compute/堆栈限额、~30 个 syscall          │
└──────────────────┬──────────────────────────┘
                   │ 本仓只暴露其中能 fail-closed 抽出的子集
                   ▼
┌─────────────────────────────────────────────┐
│ 2. Lean 编译剖面（本仓产品）                 │
│    普通 def + Profile + Extract + Emit      │
└──────────────────┬──────────────────────────┘
                   │ 需要组合其它程序时，再加具名 recipe
                   ▼
┌─────────────────────────────────────────────┐
│ 3. 封闭 callee 目录（应用协议，不是语言）     │
│    System / Token / ATA / Memo …            │
│    权威在 interface crate + 链上程序，       │
│    不在 solana-program 核心                 │
└─────────────────────────────────────────────┘
```

ProofForge 同时做了 2 的一部分（用自己的 DSL）和 3 的一批 recipe。对照它只为了少踩 ABI 坑，不为了抄功能面。

## 第 1 层：官方运行时（规划必须读）

出处（2026-08-22 读过）：

| 文件 | 钉什么 |
|---|---|
| [Programs](https://solana.com/docs/core/programs) | 程序无状态；状态在数据账户；sBPF ELF；堆 32KiB / 可调 256KiB；栈帧 4096；调用深度 64；CPI 栈 5 |
| [Accounts](https://solana.com/docs/core/accounts) | 每账户五字段：lamports / data / owner / executable / rent_epoch；只有 owner 能改 data、扣 lamports |
| [CPI](https://solana.com/docs/core/cpi) | `invoke` / `invoke_signed`；特权只能向下延伸；账户必须由调用方传入 |
| [Limitations](https://solana.com/docs/programs/limitations) | 官方 Rust 也禁 fs/net/thread/rand；float 是软实现；Bincode/格式化很贵 |
| [Syscall reference](https://solana.com/docs/core/programs/syscall-reference) | `create_program_runtime_environment_v1()` 登记的全部 syscall |
| [Sysvars](https://docs.anza.xyz/runtime/sysvars) | `get()`：Clock / EpochSchedule / Fees / Rent / EpochRewards；SlotHistory 链上读不了 |

entrypoint 形状（官方 native Rust 教程）：

```
process_instruction(program_id, accounts: &[AccountInfo], instruction_data: &[u8])
```

本仓已经实现的是这三件事的一个切片：单账户 `AccountInfo`、instruction data 里的 disc+u64、Loader V3 序列化。缺的是同一契约的其余部分，不是 PF 的 MiniAmm。

### syscall 目录 = VM 能做的事

按官方分类，本仓只应对其中能写成普通 Lean、且能 fail-closed 抽出的项。feature-gated 默认关。

| 类 | 官方 syscall（摘） | 本仓 |
|---|---|---|
| 停机 | `sol_panic_` | 已有：overflow / Custom(1) `exit` |
| 日志 | `sol_log_*` | 不做产品语义；调试可后加 |
| 返回 | `sol_set_return_data` / `sol_get_return_data` | set 已有；get 在 CPI 后才需要 |
| 哈希 | `sol_sha256` / keccak / blake3 / poseidon | `sol_sha256` / `sol_keccak256` 已绿（首 u64）；blake3 / poseidon 仍 FC |
| 曲线 / 配对 | curve25519 / alt_bn128 / big_mod_exp | 默认关 |
| CPI | `sol_invoke_signed_c` / rust | L4 封闭 recipe 才开 |
| PDA | `sol_try_find_program_address` / create | L4 |
| sysvar | `sol_get_clock_sysvar` 等 | L4；unixTime 仍 FC（PF 也 FC） |
| 内存 | memcpy / memcmp / alloc_free | memcpy 由发射器自用；`alloc_free` 新部署已禁用 |
| 计算 | `sol_remaining_compute_units` | 不做业务语义 |

「补全」的意思是：第 1 层里、第 2 层决定暴露的那些格子变绿。不是 30 个 syscall 全开。

## 第 2 层：Lean 剖面（本仓真正要补的）

权威是 Lean 能证的转移函数，加上能降到第 1 层的子集。

必须补（相对现在的 Counter/Pair 模板）：

- 入口标记与按名 discriminator（同一程序多个 mutate/view）
- 任意 `ite` / 比较 / checked 四则
- 状态叶子：窄整数、Option、定长 Array
- N 个入口；init 写全字段
- 内容寻址 digest（证明主语 = 编译主语）

这不是 SDK 功能，是「普通 Lean 怎么说到官方 entrypoint」。

官方 Rust 教程用 `entrypoint!` + `process_instruction`。本仓对应物是 `@[solana_entry]` + 抽出器。两边都不是「任意宿主语言」。

[Limitations](https://solana.com/docs/programs/limitations) 是直接类比：Rust 上链禁 `std::fs` / `thread` / `rand`；Lean 上链禁 `IO` / `partial` / `sorry` / 一般递归。依据相同——确定性、单线程、计量。

## 第 3 层：其它程序（不要写进语言）

官方把 crate 拆开了，本仓也该拆：

| crate | 角色 | 本仓怎么用 |
|---|---|---|
| [`solana-program`](https://docs.rs/solana-program/latest/solana_program/) | 链上「标准库」：entrypoint、AccountInfo、CPI、sysvar、一部分 native ID | **读文档理解契约**；不实现它的模块树 |
| [`solana-sdk`](https://solana.com/docs/clients/official/rust) | 链下客户端 | 不做 |
| [`pinocchio`](https://solana.com/docs/clients/official/rust) | 另一套 Rust 链上库，仍开发中 | 不跟 |
| `solana-system-interface` | System 程序指令 | L4 一条封闭 recipe |
| `spl-token-interface` / ATA / memo | 其它链上程序 | 各一条 recipe；Token-2022 默认不做 |

System / Token 不是「语言特性」。它们是链上已部署程序。本仓要做的是：Lean 里写一次 `system.transfer` 的账户表 + 指令字节，发射 `invoke`。PF 已经走通若干条，可以当 ABI 夹具，权威仍是 interface crate 和链上程序。

`solana-program` 文档自己也写了：crate 同时给链上和链下编，**有些符号链上没有，有些链下会炸**，文档分得不好。所以不能拿它的 module 列表当完成定义。

## 规划时读什么、不读什么

**读（做规划 / 开 L4 之前）**

- 上面第 1 层那 6 个官方页
- 具体 recipe 的 interface crate（System transfer、Token `transferChecked`）
- Loader V3 序列化（本仓已钉进 Emit；改 `dataLen` 必须重算偏移——Pair 已踩过）

**对照着读（省时间，不当地板）**

- PF StateCell / TransferSol / CallerIsMe 的账户检查顺序
- PF 已算过的 layout marker / disc 公式（本仓已复用域名前缀）

**不读来当 backlog**

- PF MiniAmm / Map / pf.assets / TokenJar 功能清单
- `solana-program` 的全部 re-export（borsh1、bpf_loader 指令构造、program_stubs…）
- Anchor 宏表面
- Pinocchio

## 对现有 L1–L4 的修正

[gap-vs-proofforge.md](gap-vs-proofforge.md) 的阶段仍对，依据改成上面三层：

| 阶段 | 对哪一层 | 完成定义 |
|---|---|---|
| L1 | 第 2 层说清官方 entrypoint | 属性、disc、if/算术、digest |
| L2 / L3 | 第 1 层的账户 `data` 布局 | 叶子类型、N 入口 |
| L4 | 第 1 层 syscall + 第 3 层一条 callee | 一条 recipe 一个任务 |

L4 开一条之前，先写清：用哪个 syscall、哪几个 AccountInfo 槽、指令字节跟哪个 interface crate 对齐、Mollusk 负例（缺 signer / 特权升级）。不要先抄 PF 的 vault 产品。

## 不因此改变的不做项

- 克隆官方 Rust SDK
- 无约束 Lean（官方 Rust 也不是无约束）
- 运行时拼的 CPI（动态 program id、remaining accounts、变长 data）。编译期钉死的 `invoke` 要做。
- Token-2022、公网、`.so` refinement
- Lean FFI → sBPF
