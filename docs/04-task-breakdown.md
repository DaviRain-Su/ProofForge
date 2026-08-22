# 04 任务拆解

阶段定义随竖切已变。S0–S5 与 fld-001/002 已交付。
缺口与不做清单：[plan/analysis/gap-vs-proofforge.md](plan/analysis/gap-vs-proofforge.md)。

## 已交付

| 阶段 | 目标 |
|---|---|
| S0 骨架 | Lake + Counter 参考语义 |
| S1 Profile | 传递闭包门 |
| S2 Extract | Expr → Ops |
| S3 Emit | 本仓 sBPF（对齐 StateCell ABI，不 import PF） |
| S4 Assemble | sbpf + Counter Mollusk 4/4 |
| S5 / fld | 单账户多字段；structure 收字段；Pair Mollusk 4/4 |

## 下一阶段

| 阶段 | 目标 | 开的条件 |
|---|---|---|
| L1 剖面 | 属性、disc、ite、四则、digest 已绿 | 完成 |
| L2 布局 | 窄整数 / Option / Vector / 无 payload 枚举已绿 | L1 绿 |
| L3 形状 | N 入口、init 全字段 | L1 绿 |
| L4 recipe | caller / clock / 封闭 CPI | 有具体第二合约 |

## L1 完成定义

- `@[solana_entry]` 标根；`#solana_build` 不再要三 ident
- increment 与 decrement 可同程序、不同 disc
- wrapping 入口仍 fail closed
- digest 变则发射变
