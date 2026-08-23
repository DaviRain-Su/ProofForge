# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。

## 已做

- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算
- `@[pf_entry]` + `#pf_build`；按名 disc；Counter 同程序 decrement
- 任意 `ite`；checked mul/div/mod；`=` `≠` 比较；Counter scale/divide/modulo/nonzero
- `IR.digestHex`（FNV-1a 64）；`#pf_build` 抽出与 fixture 必须同一 digest
- 带类型字段表：`UInt8/16/32/64` + `Option UInt64` 双叶；Flag / Maybe Mollusk
- disc / layout marker 本机 SHA-256，不再挂名表
- 定长 `Vector UInt64 n` 展开成连续槽；Window Mollusk；不定长 Array fail closed
- 无 payload 枚举作 tag；Phase Mollusk；带 payload 仍 fail closed。Bool 已在 L4-034 开成 1 字节 u8-le
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
- 账户 1 只读叶子；Peer Mollusk
- `sha256Lit`；Hash Mollusk
- 32B key / owner 按字读；Keys Mollusk
- `keccak256Lit`；Keccak Mollusk
- 账户下标叶子收口；Trio Mollusk
- Bool / `unixTime` / nonce prelude / SetAuthority owner / Approve / Multisig2；Gate / Nonce / TokenOwner / TokenMs Mollusk

## 进行中

- EVM 三大切片已交付（E-RT / E-LANG / E-ASSET）。见 [research/05-evm-coverage-slices.md](../research/05-evm-coverage-slices.md)。不做 Window。不把 SVM 名译成 EVM。
- E-OWN 已交付：Ownable + 通用 event + pair-key allowance。

## 下一刀

SVM 回 L4-cpi-invoke（把 transfer 的 walk + `sol_invoke_signed_c` 收成原语）。
再后：AccountInfo 叶子 → PDA find / invokeSigned → System create / Token+ATA。
完整清单：[analysis/sdk-surface.md](analysis/sdk-surface.md)。

能 fail-closed 抽出的格子已收口（L4-034）。

仍关、且不是延期：账户 3+ 成功路径、`ByteArray 32`、feature-gated 哈希与曲线、nonce 成功路径（要现成 nonce 账户）。

Token-2022 规划见 [analysis/token-2022.md](analysis/token-2022.md)。没有 Token v3。切片 A（换 program id）是 l5-004。hook / fee / remaining accounts 仍关。

`forBody` 已支持显式 state-carrying bounded fold 和外层参数。Phoenix N=4 扫书用
17-phase loop；free-funds ask 插入、驱逐、按 ID reduce/cancel、三种 self-trade 和
fee collection 已进真实源构建。bid book 的 free-funds collateral、驱逐、
reduce/cancel 和 sell IOC 也复用同一 fold 落地；动态树 allocator/旋转仍是后续独立范围。


完整清单：[analysis/sdk-surface.md](analysis/sdk-surface.md)。

## 其后（L2 / L3）

- 多字段 / 多构造子 inductive

## 有具体合约再开（L4）

- Token mint/burn/close、System assign/allocate、Rent exemption
- 特化仍是具名 recipe；底层是编译期钉死的 `invoke`

## 不做

- 搬 PF 前端 / `HandlerIR.mk` 私有构造
- FFI→asm；`.so` refinement；公网；运行时拼 CPI；Token-2022
- 换 Anza platform-tools
