# 模块

见 [02-architecture.md](../02-architecture.md)。

| 模块 | 合同 |
|---|---|
| [Attr](attr.md) | `@[pf_entry]` 标记 |
| [IR](ir.md) | 可哈希程序形状 + body sketch |
| [Profile](profile.md) | 传递闭包剖面 |
| [Ops](ops.md) | Expr 操作序列 |
| [Extract](extract.md) | Expr → IR + ops |
| [Emit](emit.md) | Counter → sBPF 文本（S3） |
| [Assemble](assemble.md) | `sbpf` 子进程 → `.so` + IDL |
| [Idl](idl.md) | Solana IDL spec 0.1.0 |
| [Cli](cli.md) | `pf build --target svm|evm` |
| [Runtime](runtime.md) | `clockSlot` / `signerKey0` / `acc*` 宿主 stub；抽出按名认 |
| [Evm](evm.md) | Ops → Yul / ABI / locked solc |
