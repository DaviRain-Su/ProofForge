# Backlog

- S5 续：按 ops 生成汇编片段，而不是整段 Counter 模板
- S5 已做：从 `Expr` 认出 `checkedAddU64` / `returnState` / `returnU64`
- 把本仓 IR 填进 PF `HandlerIR`（`IR.mk` 私有，需 capability 或抽出公共构造）
- attribute `@[solana_entry]` elaborator（S2 可做，非 S0）
- 多账户 / CPI recipe
- IR 内容寻址 digest
- `.so` refinement（明确不在 v0）
- 换 Anza platform-tools（无强理由不换）
