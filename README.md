# solana-lean

Lean 4 的 **Solana 编译剖面**：普通 `def` 写合约，普通 `theorem` 证合约。不是一门新合约语言。

当前：**竖切已通 + S5 抽出认出 checked-add**。下一步按 ops 生成汇编，替换整段模板。

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
(cd runtime-tests/solana && SOLANA_LEAN_COUNTER_SO=../../build/sbpf/Counter.so cargo test --test counter)
```

Toolchain：`leanprover/lean4:v4.31.0`（与 ProofForge 对齐）。

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。可行性：[docs/research/03-feasibility.md](docs/research/03-feasibility.md)。
