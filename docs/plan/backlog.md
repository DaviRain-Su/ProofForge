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

## 下一刀

完整清单：[analysis/sdk-surface.md](analysis/sdk-surface.md)。

建议下一条：L4-pda-find + L4-cpi-signed。
再后：System create / Token+ATA。

## 其后（L2 / L3）

- 多字段 / 多构造子 inductive

## 有具体合约再开（L4）

- Token mint/burn/close、System assign/allocate、Rent exemption
- 特化仍是具名 recipe；底层是编译期钉死的 `invoke`

## 不做

- 搬 PF 前端 / `HandlerIR.mk` 私有构造
- FFI→asm；`.so` refinement；公网；运行时拼 CPI；Token-2022
- 换 Anza platform-tools
