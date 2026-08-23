# 模块

见 [02-architecture.md](../02-architecture.md)。

| 模块 | 合同 |
|---|---|
| [Crypto](crypto.md) | 本机 SHA-256 / Keccak-256 |
| [Attr](attr.md) | `@[pf_entry]` 标记 |
| [IR](ir.md) | `Core.IR` 可哈希程序形状 + `Svm.ABI` 物理布局 |
| [Profile](profile.md) | 传递闭包剖面 |
| [Ops](ops.md) | Expr 操作序列 |
| [Extract](extract.md) | Expr → IR + ops；任意用户项目 |
| [Phoenix](phoenix.md) | 独立项目：双边 bounded N=4 price-time FIFO IOC |
| [Svm](svm.md) | Ops → sBPF / IDL / locked sbpf |
| [Solanalib](solanalib.md) | Core/SVM target IR → bounded typed sBPF semantics |
| [Emit](emit.md) | `Svm.Emit`：Counter → sBPF 文本 |
| [Assemble](assemble.md) | `Svm.Assemble`：`sbpf` 子进程 → `.so` + IDL |
| [Idl](idl.md) | `Svm.Idl`：Solana IDL spec 0.1.0 |
| [Cli](cli.md) | `pf build --target svm|evm` |
| [Runtime](runtime.md) | `Svm.Runtime` / `Evm.Runtime` 宿主 stub；抽出按名认 |
| [Evm](evm.md) | Ops → Yul / ABI / locked solc |
