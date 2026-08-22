# solana-lean

Lean 4 的 **Solana 编译剖面**：普通 `def` 写合约，普通 `theorem` 证合约。不是一门新合约语言。

当前：**L4 SDK 表面**。`clockSlot` / `signerKey0` 是普通 Lean 名，抽出后走 syscall / `ACC0_KEY`。补全依据见 [docs/plan/analysis/authority.md](docs/plan/analysis/authority.md)。

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
  cargo test --locked --test counter --test pair --test flag --test maybe --test window --test phase --test choice --test clock --test transfer)
```

Toolchain：`leanprover/lean4:v4.31.0`（与 ProofForge 对齐）。

EVM 平行剖面（同一 `Examples.Counter`，不搬 PF DSL）：

```bash
lake exe evmLeanAssemble -- build/evm
# 写出 Counter.yul / Counter.abi.json / Counter.bin
# 要求本机 solc 恰好 0.8.34
FOUNDRY_BIN=$HOME/.foundry/bin runtime-tests/evm/anvil_counter.sh
FOUNDRY_BIN=$HOME/.foundry/bin runtime-tests/evm/anvil_pair.sh
# constructor / increment / get / overflow；Pair 双槽 + right 保持；缺 anvil/cast 则 skip
```

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。可行性：[docs/research/03-feasibility.md](docs/research/03-feasibility.md)。
