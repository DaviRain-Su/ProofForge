# SolanaLean.Emit

## Purpose

把 v0 Counter IR 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

Load 由 `Val` 决定：`.field _ name` → `ACC0_DATA + fieldOffset`；`.arg _` → `INSTRUCTION_DATA+8`；`.clockSlot` → 40 字节栈缓冲 + `sol_get_clock_sysvar` + `ldxdw` 第一字；`.signerKey0` → `ACC0_KEY+0`；`.accLamports0` / `.accOwner0` / `.accDataLen0` / `.accN` 读对应 header 字；`.isSigner0` / `.isWritable0` / `.isExecutable0` 读 header +1/+2/+3；`.findPda seed` → `sol_try_find_program_address`（一条 ASCII 种子 + 当前 program id），返回 bump。用到 `signerKey0` 的入口 `needSigner=true`；只读旗叶子不强制签名。`invoke` 走 N 账户虚地址 walk + `sol_invoke_signed_c`。metas 相对已加 `metaOff` 的 `r5`，第 i 条在 `16*i`，不要再加 16。`systemTransfer` 是 program=2 / metas 两槽 / `u32le(2)||u64le` 的特化。acc0 以及 meta 标 writable/signer 的账户在 prelude 里检查。按槽宽用 `ldxb`/`ldxh`/`ldxw`/`ldxdw` 与对应 `stx*`。layout marker 与 `INSTRUCTION_DATA*` 按 `Program` 取。dispatch 按每个 method 的 `ixName` 取已登记 discriminator。`okState` 写回目标取同序列 checked 算术的 lhs（Pair.creditLeft 抽出的 `okState (field right)` 仍写 left）。有 `_tag` 槽时 `okState (lit 0)` 清零两叶，其它值写 tag=1 + payload。字面量用十六进制，避免 `sbpf` 拒 `2^64-1`。空 ops 失败。

## API

`emitCounterAsm : IR.Program → Except String String`

汇编头含 `digest=`（`IR.digestHex`）。

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean`：含 `entrypoint`、checked-add overflow、layout marker、三 discriminator、`sol_set_return_data`；空 IR 拒绝。
