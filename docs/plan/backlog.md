# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。

## 已做

- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算

## 下一刀（L1，按这个顺序开任务）

1. `@[solana_entry]` + `#solana_build`（不必手写三 ident）
2. 按方法名算 discriminator；同一程序可编 increment 与 decrement
3. 任意 `ite` 树；checked mul/div/mod；更多比较
4. `Program` 内容寻址 digest（证明主语 = 编译主语）

## 其后（L2 / L3）

- 窄整数叶子；Option / 定长 Array；layout marker 改本机 SHA-256
- N 入口；`init` 写全字段；只读 view 返回任意已布局叶子

## 有具体合约再开（L4）

- caller / clock
- 封闭 `system.transfer`、Token `transferChecked`、vault PDA
- 每条都是具名 recipe，不是通用 CPI

## 不做

- 搬 PF 前端 / `HandlerIR.mk` 私有构造
- FFI→asm；`.so` refinement；公网；通用 CPI；Token-2022
- 换 Anza platform-tools
