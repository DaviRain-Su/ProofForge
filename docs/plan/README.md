# 交付计划

分析：[analysis/v0-slice.md](analysis/v0-slice.md) · [analysis/authority.md](analysis/authority.md) · [analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)

任务：

| ID | 状态 | 内容 |
|---|---|---|
| [skel-001](tasks/skel-001.md) | done | Lake 骨架 + Counter 参考语义 |
| [prof-001](tasks/prof-001.md) | done | Profile 传递闭包 |
| [extr-001](tasks/extr-001.md) | done | Expr 抽出 |
| [lowr-001](tasks/lowr-001.md) | done | 本仓 Counter sBPF 发射（对齐 PF StateCell） |
| [asmb-001](tasks/asmb-001.md) | done | sbpf + Mollusk 4/4 |

| [gen-001](tasks/gen-001.md) | done | Expr → checkedAdd 操作序列 |
| [gen-002](tasks/gen-002.md) | done | 按 Op 选择 handler 体 |
| [gen-003](tasks/gen-003.md) | done | 按 Val 生成 load |
| [gen-004](tasks/gen-004.md) | done | 单账户 UInt64 表达式编译器 + decrement |
| [fld-001](tasks/fld-001.md) | done | 多字段 UInt64 布局 + Pair |
| [fld-002](tasks/fld-002.md) | done | 从 structure 收字段 + Pair .so |
| [l1-001](tasks/l1-001.md) | done | 属性入口 + 按名 disc + 多 mutate |
| [l1-002](tasks/l1-002.md) | done | 任意 ite + checked mul/div/mod |
| [l1-003](tasks/l1-003.md) | done | Program 内容寻址 digest |
| [l2-001](tasks/l2-001.md) | done | 带类型字段表 + Option 双叶 |
| [l2-002](tasks/l2-002.md) | done | 定长 Vector UInt64 n |
| [l2-003](tasks/l2-003.md) | done | 本机算出 disc 与 layout marker |
| [l2-004](tasks/l2-004.md) | done | 无 payload 枚举作 tag |
| [l3-001](tasks/l3-001.md) | done | init 写全字段 + view 任意叶子 |
| [l3-002](tasks/l3-002.md) | done | Option match 读 payload |
| [l3-003](tasks/l3-003.md) | done | 单字段用户 inductive 作 tag+payload |
| [l4-001](tasks/l4-001.md) | done | clock.slot + account-0 signer key |
| [l4-002](tasks/l4-002.md) | done | 封闭 system.transfer |
| [l4-003](tasks/l4-003.md) | done | 编译期钉死的 invoke 原语 |
| [l4-004](tasks/l4-004.md) | done | 账户 0 AccountInfo 只读叶子 |

积压：[backlog.md](backlog.md)
SDK 剩余面：[analysis/sdk-surface.md](analysis/sdk-surface.md)
