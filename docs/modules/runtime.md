# SolanaLean.Runtime

## Purpose

普通 Lean 名，抽出后变成 syscall / AccountInfo 读。不是新 DSL。

## Surface

- `clockSlot : UInt64` — 链上 `sol_get_clock_sysvar` → `Clock.slot`（物理 slot）。宿主 `@[irreducible]` stub，值是 0，不要 unfold。
- `signerKey0 : UInt64` — 链上 `ACC0_KEY+0` 第一个小端 u64。用到该叶子的入口检查 `is_signer`。不是 `tx.origin`。
- `systemTransfer lamports` — 封闭 `system.transfer`。三账户 payer/recipient/System，`sol_invoke_signed_c`，无 signer seeds。
- EVM 叶（SVM 发射器一律拒）：`evmTimestamp` / `evmChainId` / `evmSelf` / `evmCallValue` / `evmSelfBalance` / `evmCaller`（低 8B）/ `evmBlockNumber` / Addr20 三叶 `evmCallerW0..W2`、`evmSelfW0..W2`（w2 仅低 4 字节）。
- `evmDeposit amt` — `eq(callvalue(), amt)`，入口变 payable。
- `evmSendEth w0 w1 w2 amt` — 组装 20B 后 value `CALL`，失败 revert。重入不进参考语义。
- `evmLogTipped amt` — LOG1 topic = keccak(`Tipped(uint64)`)。
- `evmMapGetU64` / `evmMapSetU64` — hashed `Map UInt64 UInt64`：`keccak256(key || base)` → occ + payload。
- `evmMapGetAddr` / `evmMapSetAddr` — hashed `Map Addr20 UInt64`：`keccak256(w0||w1||w2||base)`。
- `evmTokenTransfer` — 封闭 ERC-20 `transfer`；返回 0 或 32 非零。
- `evmTokenBalanceOfSelf` — `STATICCALL balanceOf(address(this))`，超 UInt64 revert。

`unixTime`、完整 32B key、独立 caller 账户、通用 CPI 本切片 fail closed。不把 SVM 名译成 EVM opcode。

## Tests

`Examples/Clock.lean` + `runtime-tests/solana/tests/clock.rs`：两次 `warp_to_slot`、`stamp` 写回、`key0` 缺 signer → `Custom(1)`。
