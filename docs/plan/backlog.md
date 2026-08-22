# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。

## 已做

- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算
- `@[solana_entry]` + `#solana_build`；按名 disc；Counter 同程序 decrement
- 任意 `ite`；checked mul/div/mod；`=` `≠` 比较；Counter scale/divide/modulo/nonzero
- `IR.digestHex`（FNV-1a 64）；`#solana_build` 抽出与 fixture 必须同一 digest
- 带类型字段表：`UInt8/16/32/64` + `Option UInt64` 双叶；Flag / Maybe Mollusk
- disc / layout marker 本机 SHA-256，不再挂名表

## 下一刀

L2-002：定长 `Array UInt64 n`。

## 其后（L2 / L3）

- 定长 Array
- N 入口；`init` 写全字段；只读 view 返回任意已布局叶子

## 有具体合约再开（L4）

- caller / clock
- 封闭 `system.transfer`、Token `transferChecked`、vault PDA
- 每条都是具名 recipe，不是通用 CPI

## 不做

- 搬 PF 前端 / `HandlerIR.mk` 私有构造
- FFI→asm；`.so` refinement；公网；通用 CPI；Token-2022
- 换 Anza platform-tools
