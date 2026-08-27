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
        ▼
Core.Target.Registration        ← generic projection + target-owned extension callbacks
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
| `ProofForge.Core.Target` | 公共 Val/Op/Program 递归投影；静态 target registration 合同 | 具体 target extension case |
| `ProofForge.Crypto` | 本机 SHA-256 / Keccak-256 | 链上 syscall |
| `ProofForge.Svm.Runtime` / `Svm.Ops` / `Svm.IR` | Solana runtime surface、CPI/sysvar op、SVM projection registration、账户布局 | EVM storage/opcode |
| `ProofForge.Svm.EntryAdapter` | packed wire、raw/generated dispatch、physical account prefix | 协议持久状态和容器算法 |
| `ProofForge.Svm.AccountStorage` | 固定 geometry 的账户内 Region/Field、bounded Query/Call、读写 effect | transient heap、业务协议入口 |
| `ProofForge.Svm.Heap` | 官方形状的 invocation-local bounded bump allocator 模型 | 持久 Map/Queue、raw pointer surface |
| `ProofForge.Svm.ABI` | Solana discriminator / account / Loader V3 布局 | EVM selector/storage |
| `ProofForge.Svm.Emit` | Ops → Loader V3 sBPF 文本 | Yul |
| `ProofForge.Svm.Assemble` | 子进程调用 locked `sbpf` | FFI |
| `ProofForge.Svm.Idl` | Solana IDL spec 0.1.0 | ABI JSON |
| `ProofForge.Evm.Runtime` / `Evm.Ops` / `Evm.IR` | EVM runtime surface、opcode、EVM projection registration、storage slot、selector | Loader V3 / CPI |
| `ProofForge.Evm.Sdk` | EVM 合同侧类型、静态 storage cursor、typed map、context / immutable / event / revert / closed-call facade | SVM account bytes、业务协议、runtime layout object |
| `ProofForge.Evm.Component` | 稳定 Query/Call 桥；hashed-map / wide-word / closed-call 已迁入 | 任意 CALL、SVM 账户几何 |
| `ProofForge.Evm.Emit` / `Evm.Assemble` | Yul / ABI / locked solc | sBPF / IDL |

## SVM 组合边界

Queue、Map、allocator 或具体协议 instruction 不是新的顶层指令集。它们按生命周期组合：

```diagram
┌──────────────────────┐
│ 普通 Lean source 语义 │
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Core CFG / typed effect│  checked scalar、分支、effect ordering
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Svm.EntryAdapter      │  wire、账户前缀、raw/generated route
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Svm.AccountStorage    │  account-resident Map/Queue/allocator/tree
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ target-owned backend │  frame、CPI/PDA/syscall、sBPF
└──────────────────────┘

┌──────────────────────┐
│ Svm.Heap              │  bounded transient scratch only
└──────────────────────┘
```

`AccountStorage.Region/Field` 固定 account/base/stride/capacity/index base，`Query/Call` 携带
arity、geometry、canonical digest 与 transitive read/write effects。新容器能力优先扩展这套
target-owned vocabulary；主 Extract/IR/Emit 只保留一个 generic storage bridge，不能出现
Phoenix、订单类型或某个账户偏移的特判。PDA/CPI 只在遇到一种此前无法表达的链上字节形状
时扩展通用 seed/word/meta vocabulary，而不是为协议 wrapper 增加 recipe opcode。

持久内存和 transient heap 严格分离。官方 SVM allocator 的 `Vec`/`Box` 等 allocation 只在
一次 invocation 内存活，默认 32 KiB、可请求到 256 KiB，向下 bump 且 `dealloc` 不回收；
任何 native pointer/capacity 都不能写进账户。持久 Map/Queue 使用账户 bytes 上的固定容量
index/offset/POD 视图，零或 one-based sentinel 由 descriptor 明确声明。

## EVM 组合边界

EVM 与 SVM 共享普通 Lean、Profile、Extract 和 Core CFG，但不共享物理存储模型。
`Evm.Sdk` 是合同源代码到既有 EVM component/runtime 的稳定 facade；静态 cursor 在抽取期
把 typed map declaration 分配到 hashed-map namespace，descriptor 不进入链上 storage。

```diagram
┌──────────────────────┐
│ 普通 Lean source 语义 │
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Evm.Sdk              │  Address/UInt256、Storage、Context、Event/Call
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Evm.Component        │  typed Query/Call、effects、canonical digest
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Evm IR / CFG / Yul   │  storage slot、ABI、selector、locked solc
└──────────────────────┘
```

SDK 不包装 `.ok` / `.error` 或改变 Lean 控制流；这些形状仍由合同函数显式表达并由 Extract
fail closed 处理。这样抽象 storage/effect vocabulary，而不让 facade 隐藏状态写入或改变 IR。

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
