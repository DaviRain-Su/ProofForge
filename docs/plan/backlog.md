# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。

## 已做

- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算
- `@[solana_entry]` + `#solana_build`；按名 disc；Counter 同程序 decrement
- 任意 `ite`；checked mul/div/mod；`=` `≠` 比较；Counter scale/divide/modulo/nonzero
- `IR.digestHex`（FNV-1a 64）；`#solana_build` 抽出与 fixture 必须同一 digest
- 带类型字段表：`UInt8/16/32/64` + `Option UInt64` 双叶；Flag / Maybe Mollusk
- disc / layout marker 本机 SHA-256，不再挂名表
- 定长 `Vector UInt64 n` 展开成连续槽；Window Mollusk；不定长 Array fail closed
- 无 payload 枚举作 tag；Phase Mollusk；带 payload / Bool 仍 fail closed
- 多个 init；`init` paramCount 按 λ 算；Pair `initBoth` / `getRight`
- `Option UInt64` match 读 payload；Maybe.getValue Mollusk
- 单字段用户 inductive 作 tag+payload；Choice Mollusk
- `clockSlot` + 账户 0 `signerKey0`；Clock Mollusk
- 封闭 `system.transfer`；三账户虚地址 walk + `sol_invoke_signed_c`；Transfer Mollusk
- 编译期钉死的 `invoke`；`systemTransfer` / `invokeAcc1` 共用发射器；Ping Mollusk
- 账户 0 AccountInfo 只读叶子（lamports / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗）；Info Mollusk
- 表层通用 `invoke`；`systemTransfer` / `invokeAcc1` 是普通包装；Call Mollusk
- `findPda` 一条 ASCII 种子 + 当前 program id；返回 bump；Pda Mollusk
- `invokeSigned` 一组 ASCII 种子 + bump；Signed Mollusk（错 bump 失败）
- `systemCreate` 普通包装；owner = 当前 program id；Create Mollusk
- `tokenTransferChecked` 普通包装；Token `TransferChecked`；TokenXfer Mollusk
- `ataCreateIdempotent` 普通包装；ATA CreateIdempotent；Ata Mollusk
- `rentExemption` 叶子；`sol_get_rent_sysvar` × `(128+n)`；Rent Mollusk
- `tokenMintToChecked` / `tokenBurnChecked`；TokenMint Mollusk
- `systemAssign` / `systemAllocate`；SysAlloc Mollusk
- `tokenInitAccount` / `tokenCloseAccount`；TokenAcc Mollusk
- `memoWrite`；Memo Mollusk
- `createPda`；CreatePda Mollusk
- `checkPda`；Pda Mollusk 验证 bump
- `tokenApproveChecked` / `tokenFreezeAccount` / `tokenThawAccount`；TokenApprove / TokenFreeze Mollusk
- `clockEpoch`；Clock Mollusk 两次 warp 跨 epoch
- `tokenSetMintAuthority` / `tokenRevoke`；TokenAuth Mollusk
- `slotsPerEpoch`；Epoch Mollusk 改 schedule
- `tokenAccountSize` / `cpiReturn`；TokenSize Mollusk 返回 165
- `systemAllocateWithSeed`；SysSeed Mollusk
- `systemCreateWithSeed`；SysSeed Mollusk 转 lamports
- `systemAssignWithSeed`；SysSeed Mollusk 改 owner
- `systemTransferWithSeed`；SysXfer Mollusk
- `tokenInitMint`；TokenMint2 Mollusk
- `tokenSyncNative`；TokenNative Mollusk

## 下一刀

完整清单：[analysis/sdk-surface.md](analysis/sdk-surface.md)。

剩余可开、仍落在现有抽出/发射器上：

1. Token classic 常用指令已绿；Multisig / Token-2022 仍关
2. `sol_get_return_data` 单独叶子已随 L4-022 开出；无 CPI 仍 Custom(1)

nonce / Token-2022 / remaining accounts / 运行时 program id 仍关。

## 其后（L2 / L3）

- 多字段 / 多构造子 inductive

## 有具体合约再开（L4）

- Token mint/burn/close、System assign/allocate、Rent exemption
- 特化仍是具名 recipe；底层是编译期钉死的 `invoke`

## 不做

- 搬 PF 前端 / `HandlerIR.mk` 私有构造
- FFI→asm；`.so` refinement；公网；运行时拼 CPI；Token-2022
- 换 Anza platform-tools
