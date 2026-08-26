# ProofForge.Svm.Emit

## Purpose

把 target-owned SVM CFG 发射成与 ProofForge StateCell 对齐的 sBPF 汇编文本。

## Boundary

公开入口先调用 `Svm.IR.fromExtracted`；每个 target-owned `Method` 再通过 `Method.toCFG`
lower/optimize。Emitter 的 handler body 只遍历显式 basic block、edge、checked terminator 和
exit，不重新递归解释 source `ite` / `forBody`。CFG block 全部显式跳转，不依赖物理
fallthrough。全局 layout 对超过保守 12,000-instruction bound 的 edge 在物理中点插入 relay
block，迭代到所有 sBPF signed-16-bit jump 都在安全范围；不再按嵌套 branch/loop 加特判。
Core optimize 在 layout 前以结构 fingerprint 给全图 block 分桶，再做 params / instructions /
terminator 精确相等确认，合并非相邻重复 block；fingerprint collision 只增加精确比较，不会
错误共享 block。已知 redirect 在 lookup 前归一化，target extension 的静态 metadata 仍由
`payloadEq` 精确确认。

`.field _ name` 的 account-data byte offset、Vector base/stride 和 leaf width 已在 target IR
物化，emitter 不扫描 frontend flattened names 猜布局。`indexGet` / `indexSet` 的定长向量越界
走 in-bound 短前跳：`jlt r2, r3, ok_*`，越界 fallthrough `lddw r0, 0x1; exit`（Custom(1)），
再落到 `ok_*` 后的 load/store。不给每个站点独立 error label，也不用 `ja ok` 绕过。其余 Load 由 `Val` 决定：`.arg _` →
`INSTRUCTION_DATA+8`；`.clockSlot` → 40 字节栈缓冲 + `sol_get_clock_sysvar` + `ldxdw`
第一字；`.signerKey0` → `ACC0_KEY+0`；`.accLamports0` / `.accOwner0` /
`.accDataLen0` / `.accN` 读对应 header 字；`.isSigner0` / `.isWritable0` /
`.isExecutable0` 读 header +1/+2/+3；`.findPda seed` →
`sol_try_find_program_address`（一条 ASCII 种子 + 当前 program id），返回 bump。用到
`signerKey0` 的入口 `needSigner=true`；只读旗叶子不强制签名。`invoke` 走 N 账户虚地址 walk
以及 `sol_invoke_signed_c`。metas 相对已加 `metaOff` 的 `r5`，第 i 条在 `16*i`，不要再加 16。
`systemTransfer` 是 program=2 / metas 两槽 / `u32le(2)||u64le` 的特化。acc0 以及 meta 标
writable/signer 的账户在 prelude 里检查。按槽宽用 `ldxb`/`ldxh`/`ldxw`/`ldxdw` 与对应
`stx*`。layout marker 与 `INSTRUCTION_DATA*` 按 `Program` 取。dispatch 按每个 method 的
`ixName` 取已登记 discriminator。CFG dataflow 跟踪 checked result / explicit store 穿过
edge；不一致的 join fail closed。`okState` 写回目标取 checked 算术的 lhs
（Pair.creditLeft 抽出的 `okState (field right)` 仍写 left）。同序列已有 `storeField` 时
`okState` 只回传、不再猜 dest。`storeField name v` 把 `v` 写进名为 `name` 的槽。有 `_tag`
槽时 `okState (lit 0)` 清零两叶，其它值写 tag=1 + payload。字面量用十六进制，避免 `sbpf`
拒 `2^64-1`。所有会生成分支 label 的递归 `loadVal` 叶子都带 method / block scope，
同一入口多次读取 clock、PDA、rent 等叶子不会产生重名 label。空 ops 失败。多返回值由
CFG tuple exit 一次写入 return-data，不丢弃第一项之后的值。

## API

`emitProgramAsm : Extract.IR.Program → Except String String`；`emitAsm` 接受 target-owned
`Svm.IR.Program`。`emitCounterAsm` 仅是 legacy compatibility 入口。

汇编头含 `digest=`（`Core.IR.digestHex`）。

非 Counter 形状 → `extract/unsupported`。

## Tests

`Tests/EmitSpec.lean` / `Tests/CFGSpec.lean`：含 `entrypoint`、checked edge、layout marker、
discriminator、tuple exit 与 `sol_set_return_data`。`Tests/PhoenixSpec.lean` 钉 CFG block、全局
relay 和无未解析 edge token；实际 ELF 汇编及 48 个 Mollusk 文件由 CI 覆盖。
