# ProofForge.Svm.Solanalib

## Purpose

用 Solana Foundation 的 `leanprover-solanalib` 做一个**有界 typed sBPF semantics bridge**，
验证新的 `Core.Evaluation → Svm.IR physical layout → sBPF instruction` 边界是否可行。
它不是新 frontend，也不替换 Extract、SVM emitter 或 `sbpf` assembler。

依赖固定在 upstream commit `6c115ef1ef6a0cde8dbd6fd875b7dc87d60939ec`；两仓都使用
Lean 4.31.0。上游无 encoder / textual assembler，因此这里直接生成
`Solanalib.SBPF.BpfInstruction`，不假装能解析现有 `.s`。

## Implemented experiment

- `staticStoreInstruction?`：把 `Svm.IR.Slot(offset,width)` 变成 typed
  `st m8|m16|m32|m64 br6 valueReg (ACC0_DATA + offset)`；拒不支持的 width 和超过正 signed
  16-bit 的 offset。
- `staticStoreAt?`：先用 Core `Place` 在 SVM target layout 中找槽，再生成 typed store；不按
  flattened field name 猜位置。
- `checkedArithBody`：把 Core checked add/sub/mul/div/mod 的成功路径变成
  `mov64 r4,r1; op64 r4,r2`。当前 emitter 使用 classic `alu64 mul/div/mod`，所以该 fragment
  明确选择 Solanalib `.v1`；`checkedArithBody_verified` 证明五种 body 都通过上游 instruction
  verifier，`evalCheckedArithBody_corresponds` 证明 source guard 成功时五种 typed fragment
  都在 `r4` 产生对应的 64-bit word result。
- `checkedArithGuard`：物化当前 emitter 的五种 source success condition；add/sub/mul 排除
  wrap，div/mod 排除零除数。
- `checkedWriteFragment?`：从实际 `Core.StateWrite` 取 checked kind，从实际 `Svm.IR.Program`
  取 typed physical destination，合成一个 bounded compute+store fragment。
- `evalCheckedArithBody` / `evalStaticStore?` / `evalCheckedWrite?` 直接调用上游 ALU / memory
  semantics。`checkedAddWrite_simulates` 证明 Counter 真实 value slot 上，source add guard 成功时，
  typed ALU+store 把精确和交给上游 `storev`。测试固定正常 add/sub、machine wrap、64-bit
  store/load round trip，以及 invalid width/offset fail closed。
- `checkedCFGWriteFragment?`：同时读取 target-owned SVM CFG 的 checked arithmetic terminator、
  `Core.StateWrite` 和 physical slot；只在 lhs/rhs、目标 place/field、零参数 success/overflow
  edge 全部一致时，生成 typed control fragment。success 路径保留 emitter 的
  `r4 → [r10-24] → r1 → account data` handoff 和显式 `ja`，overflow 路径在任何 store 前离开。
- `evalCheckedCFGWrite` 用上游 small-step `step` 按 decoded PC 执行五种真实 guard/body；这会
  正确处理 multiply zero path 跳过 quotient guard，而不是按 list 顺序误执行除零。
  `evalCheckedGuard_corresponds` 对任意 kind/lhs/rhs 证明 emitter guard 恰好选择 source
  success/overflow condition 且不改内存；`checkedControl_selects_success` 和
  `checkedControl_overflow_preserves` 给出两条通用 edge theorem。
- `cfgBranchFragment?` 从真实 target-owned SVM CFG branch 保留 cmp/lhs/rhs/then/else identity，
  拒绝尚未 lowering 的 argumented edge，并生成 emitter 对应的
  `j<cmp> r1,r2,then; ja else` decoded pair。`evalCFGBranch_corresponds` 直接通过上游 `step`
  证明 eq/ne/lt/le/gt/ge 六种 unsigned 比较选择同一 Core edge 且内存不变。

旧的通用 guard/body API 仍刻意分层：Solanalib 的 `BitVec 64` 正确暴露 wrap
（`u64Max + 1 = 0`），`evalCheckedWrite?` 只在 source guard 成功后执行 typed body 和 store；
新的 CFG slice 则把五种 guard edge、scratch handoff 与 store 放进同一个可执行 fragment。

上游另有 machine-layer `SBPF.U128 := BitVec 128`，但用途是 wide multiply，不是
high-level Program ABI 或 Borsh codec；`Solanalib.Pubkey` 仍包 `ByteArray`，其 32-byte
长度约束也尚未进入类型。因此 Phoenix 的 `client_order_id` 不把 SVM `BitVec` 泄漏到
Core，而用 target-neutral little-endian `(lo, hi) : UInt64 × UInt64`；未来 32-byte key
同样应先用固定长度 Core layout，再由 SVM adapter 编 wire bytes。

## Non-goals / remaining trust boundary

Solanalib 当前没有为本仓提供：

- Solana Loader account/instruction-data serialization；
- account signer/writable/owner/data bounds；
- syscall、sysvar、PDA、CPI 或 `sol_invoke_signed` host semantics；
- ELF、linker、relocation、loader acceptance；
- textual assembly parser 或 instruction encoder；
- `u128` / Pubkey / Borsh 的 protocol codec 与长度/round-trip 证明；
- high-level `Account` / `Instruction` 到 SBPF memory 的 refinement；
- 完整 Agave verifier（上游 verifier 只覆盖 instruction-level version/divisor 条件）。

这仍不是完整 emitter refinement；目前只覆盖 checked arithmetic/static write 和普通
CFG branch，不覆盖 operand materialization、任意 block body 或 whole-program execution。

## Tests

- `Tests/SolanalibSpec.lean`：上游 executable semantics 的 bounded characterization，以及
  五种 checked arithmetic 的 success/overflow edge、multiply zero path、scratch handoff 与
  state-store 行为；六种普通比较各覆盖 then/else decoded edge。
- `Tests/NormalizationSpec.lean`：真实抽出的 Counter increment/decrement/scale/divide/modulo
  都从 Core Place、SVM slot 和各自 target-owned CFG checked terminator 生成对应 typed
  fragment；Counter.nonzero 生成真实普通 branch fragment；任一 Core/CFG operand 不一致或
  argumented branch edge 都 fail closed。
