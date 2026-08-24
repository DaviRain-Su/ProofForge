# 02 架构

> 当前实现的权威边界见 [modules/README.md](modules/README.md) 和源码。本文中提到的
> `PF HandlerIR`、S3/S4 与 v0 是早期迁移背景；当前编译链已经是
> `Profile → Extract.IR/Core → Svm.IR | Evm.IR → target emitter`。

## 早期背景：「难的是 loading 吗」

调研里说的难头是两件不同的事，都**不是**「从磁盘加载文件」：

| 词 | 意思 | 本仓要不要重做 |
|---|---|---|
| **lowering** | 把已检查的合约语义降成 HandlerIR / sBPF 汇编 | **不重做**。ProofForge 已有 `emitSbpfAsmV1` |
| **Loader ABI** | Solana runtime 把账户数组、instruction data 喂给 `entrypoint` 的二进制布局 | **不重做**。PF 发射器已按 Loader V3 布局吐 `.s`；Mollusk 已跑通 |
| **子集检查 / 抽出** | 从普通 Lean `def` 得到可降的闭包 | **要自建**。这是本仓真正的新工作 |
| Lean FFI / runtime | 把 Lean 宿主 C 链到 sBPF | **不做** |

所以：相对从零做 Solana 后端，本仓更容易。难的那截 PF 已经付过钱。剩下是「Lean 当源语言」的薄剖面。

```diagram
普通 Lean def / theorem          ← 整段借 Lean
        │
        ▼
ProofForge.Profile 子集检查      ← 本仓自建（小）
        │
        ▼
ProofForge.Extract.IR + Core     ← target-neutral control + typed target extension
        │
   ┌────┴────┐
   ▼         ▼
Svm.IR     Evm.IR               ← 各自物化布局和 target op
   │         │
   ▼         ▼
sBPF/.so   Yul/.bin             ← Mollusk / Anvil 工程门
```

## 模块

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `ProofForge.Attr` | `@[pf_entry]` / `@[pf_inline]` 标记 | `program … where` 新语法 |
| `ProofForge.Profile` | 传递闭包准入规则 | 业务类型检查（Lean 已做） |
| `ProofForge.Extract` / `Extract.IR` | `Expr` → parameterized Core；在唯一边界组合 typed target extensions | target 物理布局 |
| `ProofForge.Core.IR` / `Core.Ops` | target-neutral schema、control、checked arithmetic | SVM syscall / EVM opcode |
| `ProofForge.Crypto` | 本机 SHA-256 / Keccak-256 | 链上 syscall |
| `ProofForge.Svm.Runtime` / `Svm.Ops` / `Svm.IR` | Solana runtime surface、CPI/sysvar op、账户布局 | EVM storage/opcode |
| `ProofForge.Svm.ABI` | Solana discriminator / account / Loader V3 布局 | EVM selector/storage |
| `ProofForge.Svm.Emit` | Ops → Loader V3 sBPF 文本 | Yul |
| `ProofForge.Svm.Assemble` | 子进程调用 locked `sbpf` | FFI |
| `ProofForge.Svm.Idl` | Solana IDL spec 0.1.0 | ABI JSON |
| `ProofForge.Evm.Runtime` / `Evm.Ops` / `Evm.IR` | EVM runtime surface、opcode、storage slot、selector | Loader V3 / CPI |
| `ProofForge.Evm.Emit` / `Evm.Assemble` | Yul / ABI / locked solc | sBPF / IDL |

## 信任边界

- **弱声明**（v0 对外）：kernel 接受了关于用户 `def` / 抽出 IR 的定理。TCB = Lean kernel + 主语绑定。
- **工程声明**：同一 IR 经 PF 发射器 + pinned `sbpf` 得到的 `.so`，在 pinned Mollusk 上行为与夹具一致。
- **不做的声明**：`.so` / loader / 全 SVM refinement。

证明主语和编译主语必须共享同一个 IR digest。禁止「证的是 A，编的是 B」。

## 早期迁移关系（历史）

以下记录解释仓库起点，不描述当前依赖边界；当前边界以上面的模块表为准。

- 本仓**不**把 PF 当用户前端。
- 本仓 **vendor / path 依赖** PF 的 Solana lowering 与 locked tool，版本冻结。
- S3 不 import PF：`IR.mk` 私有，接 capability 会拖进整仓。本仓自写 Counter 发射器，布局与 PF StateCell 黄金文件对齐。
- S4 再调 locked `sbpf`。以后若 PF 抽出公共 `HandlerIR` 构造，再换后端，不改用户 `def`。

## 早期 v0 决策（历史）

1. 表面语言 = 普通 Lean。受限 = 目标剖面，写在 `Profile`，不写在新 parser。
2. 抽出权威 = elaborated `Expr` 闭包，不是 `Lean.Compiler.IR`。
3. 后端权威 = PF 已有发射器 + `sbpf 0.2.2`（与 PF 同 pin），直到本仓有理由换钉。
4. v0 语言面 = 单账户 `UInt64` Counter，与 PF `Examples/StateCell` 行为对齐。
