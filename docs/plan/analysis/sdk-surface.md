# SDK 表面：还剩什么

依据：[authority.md](authority.md)（官方 SVM / syscall，不是 `solana-program` 模块树，也不是 PF 产品清单）。
官方 syscall 表（2026-08-22）：[Syscall reference](https://solana.com/docs/core/programs/syscall-reference)。
官方 sysvar：[Anza sysvars](https://docs.anza.xyz/runtime/sysvars)。

SDK 在本仓的意思：普通 Lean 名，抽出后变成 syscall / `AccountInfo` 读 / CPI。不是新 DSL，也不克隆 crate。

通用 CPI **要做**。否掉的只是运行时拼指令：动态 program id、变长 remaining accounts、账户表到链上才知道。那会拆掉 fail-closed 抽出。该做的是编译期钉死的 `invoke`：program id、账户下标、meta 旗、data 布局在抽出时就固定，发射 `sol_invoke_signed_c`。`systemTransfer` 是这条原语的第一条特化。

```diagram
┌──────────────────────────────────────────┐
│ 已绿                                      │
│  clockSlot / signerKey0 / systemTransfer │
└──────────────────┬───────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────┐
│ 通用 CPI 原语（要做）                      │
│  编译期钉死 program / metas / data        │
│  发射 sol_invoke_signed_c                 │
└──────────────────┬───────────────────────┘
                   │ 特化成具名 recipe
                   ▼
┌──────────────────────────────────────────┐
│ System / Token / ATA / Memo / PDA        │
└──────────────────────────────────────────┘
```

## 已绿

| Lean 名 | 降到 | 切片 |
|---|---|---|
| `clockSlot` | `sol_get_clock_sysvar` → `Clock.slot` | L4-001 |
| `signerKey0` | `ACC0_KEY+0` 首 u64；入口 `is_signer` | L4-001 |
| `systemTransfer` | 三账户 walk + `sol_invoke_signed_c`；内层 `u32le(2)\|\|u64le` | L4-002 |
| `invoke` / `invokeAcc1` | 编译期钉死 program/metas/data；N 账户 walk | L4-003 / L4-005 |
| `accLamports0` / `accOwner0` / `accDataLen0` / `accN` | 账户 0 header 只读 | L4-004 |
| `isSigner0` / `isWritable0` / `isExecutable0` | header +1/+2/+3，0 或 1 | L4-004 |
| `findPda seed` | `sol_try_find_program_address`；返回 bump | L4-006 |
| `invokeSigned` | 一组 ASCII 种子 + bump；`sol_invoke_signed_c` | L4-007 |
| `systemCreate` | System createAccount；owner = 当前 program id | L4-008 |
| `tokenTransferChecked` | Token TransferChecked；decimals 编译期常量 | L4-009 |
| `ataCreateIdempotent` | ATA CreateIdempotent；1 字节 tag 1 | L4-010 |
| `rentExemption n` | `sol_get_rent_sysvar` × `(128+n)` | L4-011 |
| `tokenMintToChecked` / `tokenBurnChecked` | Token mint / burn；decimals 编译期常量 | L4-012 |
| `systemAssign` / `systemAllocate` | System assign / allocate；owner = 当前 program id | L4-013 |
| `tokenInitAccount` / `tokenCloseAccount` | Token init3 / close；owner = acc0 公钥 | L4-014 |
| `memoWrite` | Memo 写 UTF-8 字面量；本切片 `"ok"` | L4-015 |
| `createPda` | find + System createAccount；seeds = `"vault"` | L4-016 |
| `checkPda seed bump` | `sol_create_program_address`；成功 0 / 失败 1 | L4-017 |
| overflow / Custom(1) | `exit` | L1 |
| view 返回 | `sol_set_return_data` 8 字节 | S3 |

宿主定理仍钉用户 `def`。`unixTime`、完整 32B key、独立 caller 账户仍 FC。

## 还该做：通用 CPI 原语

官方只有 `sol_invoke_signed_c` / `sol_invoke_signed_rust`。本仓走 C ABI（transfer 已通）。

Lean 表面（建议，仍是普通 def，不是 DSL）：

```
invoke (programIx : Nat) (data : …) : UInt64
invokeSigned (programIx : Nat) (data : …) (seed0 : …) : UInt64
```

抽出时必须全部已知：

| 钉死项 | 来源 | fail closed 若 |
|---|---|---|
| callee program | 外层账户下标，或字面量 32B（System 全零） | 下标非常量 / 运行时才算的 pubkey |
| 内层 metas | 编译期账户下标列表 + signer/writable | 变长 remaining / 循环里 push |
| 内层 data | 字面量前缀 + 已抽出的 `Val` 叶 | 动态长度、未布局字节 |
| signer seeds | 字面量种子 + 可选 bump 叶 | 运行时拼种子 |
| 外层账户数 | `NUM_ACCOUNTS` 下界 | 调用时才知道有几个账户 |

`systemTransfer` = `invoke` 特化：program=acc2（全零）、metas=`[(0,s+w),(1,w)]`、data=`u32le(2)||u64le(amount)`、seeds 空。Token / ATA / 用户程序走同一发射器，只换这张表。

| ID | 内容 | 完成定义 |
|---|---|---|
| L4-cpi-invoke | 无 seeds 的 `invoke`；N 账户 walk 复用 transfer | 一条非 System 的固定 callee Mollusk（可用 Memo 或 mock） |
| L4-cpi-signed | `invokeSigned` 一组种子 | PDA 付款 / vault 负例：错 bump、缺 signer |
| L4-cpi-ret | `sol_get_return_data` 8 字节 | callee 写回 u64；无 CPI 则 FC |
| L4-cpi-nacc | walk N 个账户（N 编译期常量，先 2..8） | 不再为每个 recipe 手写 ACC1/ACC2 |

仍 FC（这才是当初说「不做通用 CPI」的那截）：

- 运行时才知道的 program id
- remaining accounts / 变长账户表
- 动态 data 长度
- 多组任意 seeds
- `sol_invoke_signed_rust`（C ABI 一条就够）

## 还该做：AccountInfo 叶子（无 CPI）

这些是官方账户五元组，不是某个合约的功能。现有单账户 / 三账户 walk 已经碰到它们，只是没暴露成 Lean 名。

| ID | Lean 表面（建议） | 降到 | 完成定义 |
|---|---|---|---|
| L4-acc-lamports | `accLamports0` | `ACC0_LAMPORTS` 的 `u64` | Mollusk 读余额；不改 lamports（改要走 System） |
| L4-acc-key32 | `accKey0` | 四叶 `u64` 或后续 `ByteArray 32` | 声明 ≠ `tx.origin` |
| L4-acc-owner | `accOwner0` | owner 32B 的首 u64 或全 32B | 与当前 program id 比较可后做 |
| L4-acc-data-len | `accDataLen0` | `ACC0_DATA_LEN` | 只读 |
| L4-acc-flags | `isSigner0` / `isWritable0` / `isExecutable0` | header +1/+2/+3 | 缺 signer 负例已有，可复用 |
| L4-acc-n | `accN` | `NUM_ACCOUNTS` | 只读；不开放 remaining accounts |
| L4-signer-req | 用到 `signerKey*` 的入口强制 `is_signer` | 已有账户 0 | 扩到账户 1（独立 caller） |

多账户 walker 已为 transfer 开了一个口。后续 recipe 复用 walk，不要再写死 `ACC1_*`。

## 还该做：sysvar（有 `get()` 的才开）

官方 `get()`：Clock / EpochSchedule / Fees / Rent / EpochRewards。
`sol_get_sysvar`（SIMD-0127）feature-gated，默认关。SlotHistory 链上读不了。

| ID | Lean 表面 | syscall / 字段 | 态度 |
|---|---|---|---|
| L4-clock-slot | `clockSlot` | `sol_get_clock_sysvar` + slot@0 | **已绿** |
| L4-clock-unix | `unixTime` | 同缓冲 + unix_timestamp@32 | **保持 FC**（有符号 i64；PF 也 FC） |
| L4-clock-epoch | `clockEpoch` | epoch@16 | 可开；非常量，两次 warp 证明 |
| L4-rent | `rentExemption n` | `sol_get_rent_sysvar` + `rate*(128+n)` | **已绿** |
| L4-epoch-schedule | `slotsPerEpoch` 等一叶 | `sol_get_epoch_schedule_sysvar` | 有合约再用 |
| L4-epoch-rewards | — | `sol_get_epoch_rewards_sysvar` | 默认关 |
| L4-fees | — | `sol_get_fees_sysvar` | 已弃用，关 |
| L4-last-restart | — | `sol_get_last_restart_slot` | feature-gated，关 |

## 还该做：PDA（syscall；`invokeSigned` 的种子来源）

| ID | Lean 表面 | syscall | 约束 |
|---|---|---|---|
| L4-pda-find | `findPda seed0 …` | `sol_try_find_program_address` | 种子字面量冻结；bump 255..1；拒绝 bump 0 |
| L4-pda-create | `createPda …` | find + `system.createAccount` 一条 recipe | **已绿**；当前 program id；signer seeds 一组 |
| L4-pda-check | `checkPda seed bump` | `sol_create_program_address` | **已绿**；只验证，返回 0/1 |

没有「任意种子数组」。一条 recipe 钉死种子布局。

## 还该做：第 3 层 callee（通用 `invoke` 上的特化）

每条先写：账户表、指令字节、Mollusk 负例（缺 signer / 特权升级 / 错 program id）。权威是 interface crate + 链上程序。实现应落在 `invoke` / `invokeSigned` 上，不要再复制一套 transfer 发射器。

### System（`solana-system-interface`）

已绿：`Transfer`（tag 2）、`CreateAccount`（tag 0，52B 无 pad）、`Assign`（tag 1）、`Allocate`（tag 8）。

| ID | 指令 | 内层数据 | 账户（外层） |
|---|---|---|---|
| L4-sys-create | `CreateAccount` tag 0 | `u32le(0)\|\|lamports\|\|space\|\|owner32`（52B） | 付款人 s+w、新账户 s+w、System |
| L4-sys-assign | `Assign` tag 1 | `u32le(1)\|\|owner32` | **已绿**；账户 s+w、System |
| L4-sys-allocate | `Allocate` tag 8 | `u32le(8)\|\|space` | **已绿**；账户 s+w、System |
| L4-sys-alloc-seed | `AllocateWithSeed` / `CreateAccountWithSeed` | 后做 | 与 PDA 绑定再开 |
| L4-sys-advance-nonce 等 | nonce / authorize | — | 不做，除非有合约 |

已绿：`TransferChecked`（tag 12，10B packed）、ATA `CreateIdempotent`（tag 1）、`MintToChecked` / `BurnChecked`。

### Token classic（`spl-token-interface`，**不是** Token-2022）

| ID | 指令 | tag | 要点 |
|---|---|---|---|
| L4-tok-xfer | `TransferChecked` | 12 | mint + decimals；不要开已弃用的 `Transfer`(3) |
| L4-tok-mint | `MintToChecked` | 14 | **已绿**；mint authority signer |
| L4-tok-burn | `BurnChecked` | 15 | **已绿** |
| L4-tok-init-acc | `InitializeAccount3` | 18 | **已绿**；owner = acc0 公钥 |
| L4-tok-close | `CloseAccount` | 9 | **已绿**；lamports 退回 |
| L4-tok-approve / set-auth / freeze | — | — | 有合约再开；默认关 |

Multisig owner 默认关。

### ATA / Memo

| ID | callee | 要点 |
|---|---|---|
| L4-ata-idem | ATA `CreateIdempotent` | tag 1；账户表冻结；常跟 Token transfer 绑一条 |
| L4-memo | Memo 程序写一条 | **已绿**；只做 UTF-8 字面量；不做动态字符串 |

## 发射器自用、不暴露成 Lean 名

| syscall | 用法 |
|---|---|
| `sol_memcpy_` / `memset_` | 打包 CPI 缓冲 |
| `sol_memcmp_` | 比 32B key / program id |
| `sol_set_return_data` | 已有 view 返回 |
| `sol_get_return_data` | 仅当某条 recipe 要读 callee 返回时 |

## 明确不做（不是延期）

- 克隆 `solana-program` / Anchor / Pinocchio
- 运行时拼的 CPI（动态 program id、remaining accounts、变长 data）
- Token-2022 及全部 extension
- feature-gated：blake3 / poseidon / curve25519 / alt_bn128 / big_mod_exp / `sol_get_sysvar` / `sol_remaining_compute_units` / `sol_get_epoch_stake`
- `sol_alloc_free_`（新部署已禁用）
- `sol_log_*` 当产品语义（调试可后加，不进 digest）
- `unixTime`（有符号；PF 也 FC）
- 指令内省 `sol_get_processed_sibling_instruction` / `sol_get_stack_height`（除非有具体检查合约）
- 公网、`.so` refinement、Lean FFI → sBPF

## 建议顺序

按依赖，不是按「像 SDK」。

1. **L4-cpi-nacc + L4-cpi-invoke** — 已绿（L4-003：Ping stub）。
2. **L4-acc-*** — 账户 0 只读叶子已绿（L4-004）。完整 32B key / 账户 1 仍 FC。
3. **L4-pda-find + L4-cpi-signed** — 找 bump，再用种子签字。
4. **L4-sys-create / L4-tok-xfer / L4-ata-idem** — 特化，不再手写发射器。
5. 其余 System / Token / sysvar 有具体合约再开。

每条仍是：先写任务文件（syscall、账户、字节、负例），再改 Runtime / Extract / Emit / Mollusk。
