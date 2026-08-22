# 模块

见 [02-architecture.md](../02-architecture.md)。

| 模块 | 合同 |
|---|---|
| [IR](ir.md) | 可哈希程序形状 + body sketch |
| [Profile](profile.md) | 传递闭包剖面 |
| [Extract](extract.md) | Expr → IR |
| [Emit](emit.md) | Counter → sBPF 文本（S3） |
| Assemble | S4：`sbpf` 子进程 |
