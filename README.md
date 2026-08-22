# solana-lean

Lean 4 的 **Solana 编译剖面**：普通 `def` 写合约，普通 `theorem` 证合约。不是一门新合约语言。

当前：**L4 SDK 表面**。`clockSlot` / `signerKey0` / `acc*` / 编译期 `invoke` 是普通 Lean 名。补全依据见 [docs/plan/analysis/authority.md](docs/plan/analysis/authority.md)。

## 「难的是 loading 吗？」

不是读文件。调研里难的两截是：

1. **lowering** — 语义降成 sBPF 汇编
2. **Loader ABI** — 账户数组怎么进 `entrypoint`

这两截 ProofForge 已经有了（`emitSbpfAsmV1` + Mollusk 跑通 StateCell）。本仓要自建的是更薄的一层：从普通 Lean `def` 做子集检查和抽出。相对从零写后端，更容易，不是更难。

```
普通 Lean def / theorem     ← 借 Lean
        │
        ▼
Profile 子集检查            ← 自建（S1）
        │
        ▼
Extract Expr → IR           ← 自建（S2）
        │
        ▼
PF emitSbpf + sbpf          ← 搬（S3–S4）
```

## 构建

```bash
lake build
lake exe solanaLeanAssemble -- build/sbpf
(cd runtime-tests/solana && \
  SOLANA_LEAN_COUNTER_SO=../../build/sbpf/Counter.so \
  SOLANA_LEAN_PAIR_SO=../../build/sbpf/Pair.so \
  SOLANA_LEAN_FLAG_SO=../../build/sbpf/Flag.so \
  SOLANA_LEAN_MAYBE_SO=../../build/sbpf/Maybe.so \
  SOLANA_LEAN_WINDOW_SO=../../build/sbpf/Window.so \
  SOLANA_LEAN_PHASE_SO=../../build/sbpf/Phase.so \
  SOLANA_LEAN_CHOICE_SO=../../build/sbpf/Choice.so \
  SOLANA_LEAN_CLOCK_SO=../../build/sbpf/Clock.so \
  SOLANA_LEAN_TRANSFER_SO=../../build/sbpf/Transfer.so \
  SOLANA_LEAN_PING_SO=../../build/sbpf/Ping.so \
  SOLANA_LEAN_INFO_SO=../../build/sbpf/Info.so \
  SOLANA_LEAN_CALL_SO=../../build/sbpf/Call.so \
  SOLANA_LEAN_PDA_SO=../../build/sbpf/Pda.so \
  SOLANA_LEAN_SIGNED_SO=../../build/sbpf/Signed.so \
  SOLANA_LEAN_CREATE_SO=../../build/sbpf/Create.so \
  SOLANA_LEAN_TOKENXFER_SO=../../build/sbpf/TokenXfer.so \
  SOLANA_LEAN_ATA_SO=../../build/sbpf/Ata.so \
  SOLANA_LEAN_RENT_SO=../../build/sbpf/Rent.so \
  SOLANA_LEAN_TOKENMINT_SO=../../build/sbpf/TokenMint.so \
  SOLANA_LEAN_SYSALLOC_SO=../../build/sbpf/SysAlloc.so \
  SOLANA_LEAN_TOKENACC_SO=../../build/sbpf/TokenAcc.so \
  SOLANA_LEAN_MEMO_SO=../../build/sbpf/Memo.so \
  SOLANA_LEAN_CREATEPDA_SO=../../build/sbpf/CreatePda.so \
  SOLANA_LEAN_TOKENAPPROVE_SO=../../build/sbpf/TokenApprove.so \
  SOLANA_LEAN_TOKENFREEZE_SO=../../build/sbpf/TokenFreeze.so \
  SOLANA_LEAN_TOKENAUTH_SO=../../build/sbpf/TokenAuth.so \
  SOLANA_LEAN_EPOCH_SO=../../build/sbpf/Epoch.so \
  SOLANA_LEAN_TOKENSIZE_SO=../../build/sbpf/TokenSize.so \
  SOLANA_LEAN_SYSSEED_SO=../../build/sbpf/SysSeed.so \
  SOLANA_LEAN_SYSXFER_SO=../../build/sbpf/SysXfer.so \
  SOLANA_LEAN_TOKENMINT2_SO=../../build/sbpf/TokenMint2.so \
  SOLANA_LEAN_TOKENNATIVE_SO=../../build/sbpf/TokenNative.so \
  cargo test --locked --test counter --test pair --test flag --test maybe --test window --test phase --test choice --test clock --test transfer --test ping --test info --test call --test pda --test signed --test create --test token_xfer --test ata --test rent --test token_mint --test sys_alloc --test token_acc --test memo --test create_pda --test token_approve --test token_freeze --test token_auth --test epoch --test token_size --test sys_seed --test sys_xfer --test token_mint2 --test token_native)
```

Toolchain：`leanprover/lean4:v4.31.0`（与 ProofForge 对齐）。

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。可行性：[docs/research/03-feasibility.md](docs/research/03-feasibility.md)。
