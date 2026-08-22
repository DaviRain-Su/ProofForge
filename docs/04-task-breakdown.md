# 04 任务拆解

## 阶段

| 阶段 | 目标 | 依赖 PF lowering？ |
|---|---|---|
| S0 骨架 | Lake 工程 + 文档 + Counter 参考语义可证 | 否 |
| S1 Profile | 对声明名做白名单 / 拒绝夹具 | 否 |
| S2 Extract | 从 `increment` 的 `Expr` 抽出 IR，digest 对齐手工 IR | 否 |
| S3 Lower | IR → PF HandlerIR → `.s` | 是 |
| S4 Assemble | locked `sbpf` → `.so` + Mollusk | 本机 `sbpf`（已绿） |
| S5 Generic | `Expr` 操作序列替换 Counter 模板 | 否 |

S0–S4 已交付。S5 起见 backlog。

## S0 完成定义

- `lean-toolchain` / `lakefile.lean` / `SolanaLean.lean` 可 `lake build`
- `Examples/Counter.lean` 用普通 Lean 写三函数
- 至少一条关于 `increment` 的真定理
- 手写 `IR.Program` 描述符
- README 写清「难的不是 loading」
