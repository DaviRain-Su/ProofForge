# SDK 表面：还剩什么

依据：[authority.md](authority.md)（官方 SVM / syscall，不是 `solana-program` 模块树，也不是 PF 产品清单）。
官方 syscall 表（2026-08-22）：[Syscall reference](https://solana.com/docs/core/programs/syscall-reference)。
官方 sysvar：[Anza sysvars](https://docs.anza.xyz/runtime/sysvars)。

SDK 在本仓的意思：普通 Lean 名，抽出后变成 syscall / `AccountInfo` 读 / 一条封闭 CPI。不是新 DSL，也不克隆 crate。

```diagram
┌──────────────────────────────────────────┐
│ 已绿                                      │
│  clockSlot / signerKey0 / systemTransfer │
└──────────────────┬───────────────────────┘
                   │ 仍按「一条 recipe 一个任务」
                   ▼
┌──────────────────────────────────────────┐
│ 还该做（能写成普通 Lean、fail-closed）     │
│  AccountInfo 叶子、其余 get() sysvar、    │
│  PDA、System/Token/ATA/Memo 封闭 CPI     │
└──────────────────┬───────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────┐
│ 明确不做                                  │
│  通用 CPI、Token-2022、feature-gated 曲线、│
│  日志当产品语义、alloc_free、公网          │
└──────────────────────────────────────────┘
```

## 已绿

| Lean 名 | 降到 | 切片 |
|---|---|---|
| `clockSlot` | `sol_get_clock_sysvar` → `Clock.slot` | L4-001 |
| `signerKey0` | `ACC0_KEY+0` 首 u64；入口 `is_signer` | L4-001 |
| `systemTransfer` | 三账户 walk + `sol_invoke_signed_c`；内层 `u32le(2)\|\|u64le` | L4-002 |
| overflow / Custom(1) | `exit` | L1 |
| view 返回 | `sol_set_return_data` 8 字节 | S3 |

宿主定理仍钉用户 `def`。`unixTime`、完整 32B key、独立 caller 账户、通用 CPI 仍 FC。

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
| L4-rent | `rentExemption u64` 或 `rentLamportsPerByteYear` | `sol_get_rent_sysvar` | 开一条：exemption 计算要钉公式 |
| L4-epoch-schedule | `slotsPerEpoch` 等一叶 | `sol_get_epoch_schedule_sysvar` | 有合约再用 |
| L4-epoch-rewards | — | `sol_get_epoch_rewards_sysvar` | 默认关 |
| L4-fees | — | `sol_get_fees_sysvar` | 已弃用，关 |
| L4-last-restart | — | `sol_get_last_restart_slot` | feature-gated，关 |

## 还该做：PDA（syscall，仍不是通用 CPI）

| ID | Lean 表面 | syscall | 约束 |
|---|---|---|---|
| L4-pda-find | `findPda seed0 …` | `sol_try_find_program_address` | 种子字面量冻结；bump 255..1；拒绝 bump 0 |
| L4-pda-create | `createPda …` | find + `system.createAccount` 一条 recipe | 当前 program id；signer seeds 一组 |
| L4-pda-check | `createProgramAddress` | `sol_create_program_address` | 只验证，不找 bump |

没有「任意种子数组」。一条 recipe 钉死种子布局。

## 还该做：封闭 CPI（第 3 层 callee）

每条先写：syscall、账户表、指令字节、Mollusk 负例（缺 signer / 特权升级 / 错 program id）。权威是 interface crate + 链上程序，PF 只当 ABI 夹具。

### System（`solana-system-interface`）

已绿：`Transfer`（tag 2）。

| ID | 指令 | 内层数据 | 账户（外层） |
|---|---|---|---|
| L4-sys-create | `CreateAccount` tag 0 | `u32le(0)\|\|lamports\|\|space\|\|owner32`（52B） | 付款人 s+w、新账户 w、System |
| L4-sys-assign | `Assign` tag 1 | `u32le(1)\|\|owner32` | 账户 s+w、System |
| L4-sys-allocate | `Allocate` tag 8 | `u32le(8)\|\|space` | 账户 s+w、System |
| L4-sys-alloc-seed | `AllocateWithSeed` / `CreateAccountWithSeed` | 后做 | 与 PDA 绑定再开 |
| L4-sys-advance-nonce 等 | nonce / authorize | — | 不做，除非有合约 |

`Transfer` 已证明三账户 walk + C ABI。下一条优先 `CreateAccount`（PDA vault 需要）。

### Token classic（`spl-token-interface`，**不是** Token-2022）

| ID | 指令 | tag | 要点 |
|---|---|---|---|
| L4-tok-xfer | `TransferChecked` | 12 | mint + decimals；不要开已弃用的 `Transfer`(3) |
| L4-tok-mint | `MintToChecked` | 14 | mint authority signer |
| L4-tok-burn | `BurnChecked` | 15 | |
| L4-tok-init-acc | `InitializeAccount3` | 18 | owner 走指令数据，少一个账户 |
| L4-tok-close | `CloseAccount` | 9 |  lamports 退回 |
| L4-tok-approve / set-auth / freeze | — | — | 有合约再开；默认关 |

Multisig owner 默认关。

### ATA / Memo

| ID | callee | 要点 |
|---|---|---|
| L4-ata-idem | ATA `CreateIdempotent` | tag 1；账户表冻结；常跟 Token transfer 绑一条 |
| L4-memo | Memo 程序写一条 | 只做 UTF-8 字面量；不做动态字符串 |

## 发射器自用、不暴露成 Lean 名

| syscall | 用法 |
|---|---|
| `sol_memcpy_` / `memset_` | 打包 CPI 缓冲 |
| `sol_memcmp_` | 比 32B key / program id |
| `sol_set_return_data` | 已有 view 返回 |
| `sol_get_return_data` | 仅当某条 recipe 要读 callee 返回时 |

## 明确不做（不是延期）

- 克隆 `solana-program` / Anchor / Pinocchio
- 通用 CPI、动态 program id、remaining accounts
- Token-2022 及全部 extension
- feature-gated：blake3 / poseidon / curve25519 / alt_bn128 / big_mod_exp / `sol_get_sysvar` / `sol_remaining_compute_units` / `sol_get_epoch_stake`
- `sol_alloc_free_`（新部署已禁用）
- `sol_log_*` 当产品语义（调试可后加，不进 digest）
- `unixTime`（有符号；PF 也 FC）
- 指令内省 `sol_get_processed_sibling_instruction` / `sol_get_stack_height`（除非有具体检查合约）
- 公网、`.so` refinement、Lean FFI → sBPF

## 建议顺序

按依赖，不是按「像 SDK」。

1. **L4-acc-*** — 把已 walk 到的 AccountInfo 叶子暴露成名（lamports / key32 / flags）。不增 syscall。
2. **L4-pda-find** — `sol_try_find_program_address`，种子冻结。
3. **L4-sys-create** — 有 PDA 才能建账户。
4. **L4-tok-xfer + L4-ata-idem** — 一条 Token 转账（可拆两个任务，但要同一账户表）。
5. 其余 System / Token / sysvar 有具体合约再开。

每条仍是：先写任务文件（syscall、账户、字节、负例），再改 Runtime / Extract / Emit / Mollusk。
