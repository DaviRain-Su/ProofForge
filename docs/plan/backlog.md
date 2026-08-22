# Backlog

- S5 已做：认出 ops；按 op 种类选择 handler 体（仍是固定片段，不是任意 Expr）
- 下一步：更多 op（if / store 任意字段），真正换 def 也能编
- 把本仓 IR 填进 PF `HandlerIR`（`IR.mk` 私有，需 capability 或抽出公共构造）
- attribute `@[solana_entry]` elaborator（S2 可做，非 S0）
- 多账户 / CPI recipe
- IR 内容寻址 digest
- `.so` refinement（明确不在 v0）
- 换 Anza platform-tools（无强理由不换）
