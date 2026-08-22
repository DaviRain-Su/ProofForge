# 分析：v0 切片

## 模块分解

| 模块 | 输入 | 输出 | 依赖 |
|---|---|---|---|
| Examples.Counter | 无 | 普通 Lean 函数 + 定理 | SolanaLean.IR |
| SolanaLean.IR | 方法表 | `Program` | 无 |
| SolanaLean.Profile | 声明名列表 | accept / reject | 无（S1 加深） |
| SolanaLean.Extract | `Expr` | `Program` | Profile, IR（S2） |
| SolanaLean.Lower | `Program` | PF HandlerIR / `.s` | PF（S3） |
| SolanaLean.Assemble | `.s` | `.so` | sbpf（S4） |

## 集成

- S0：Counter → 手工 IR。无外部工具。
- S2：Extract(increment) `==` 手工 IR。
- S3：Lower 输出的 `.s` 与 PF StateCell 黄金文件在 checked-add 片段上可对照。
- S4：`.so` 走 Mollusk，行为对齐 `state_cell_shaped_product`。

## 为什么 S0 不接 PF

PF 闭包 16 万行。先把「普通 Lean 就是合约语义」钉死，避免第一刀被 Lake/依赖淹没。
