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
  verifier，`evalCheckedAdd` 证明 typed add fragment 的结果就是上游 64-bit word addition。
- `checkedArithGuard`：物化当前 emitter 的五种 source success condition；add/sub/mul 排除
  wrap，div/mod 排除零除数。
- `checkedWriteFragment?`：从实际 `Core.StateWrite` 取 checked kind，从实际 `Svm.IR.Program`
  取 typed physical destination，合成一个 bounded compute+store fragment。
- `evalCheckedArithBody` / `evalStaticStore?` / `evalCheckedWrite?` 直接调用上游 ALU / memory
  semantics。`checkedAddWrite_simulates` 证明 Counter 真实 value slot 上，source add guard 成功时，
  typed ALU+store 把精确和交给上游 `storev`。测试固定正常 add/sub、machine wrap、64-bit
  store/load round trip，以及 invalid width/offset fail closed。

guard 与 body 仍刻意分层：Solanalib 的 `BitVec 64` 正确暴露 wrap（`u64Max + 1 = 0`），
`evalCheckedWrite?` 只在 source guard 成功后执行 typed body 和 store。

## Non-goals / remaining trust boundary

Solanalib 当前没有为本仓提供：

- Solana Loader account/instruction-data serialization；
- account signer/writable/owner/data bounds；
- syscall、sysvar、PDA、CPI 或 `sol_invoke_signed` host semantics；
- ELF、linker、relocation、loader acceptance；
- textual assembly parser 或 instruction encoder；
- high-level `Account` / `Instruction` 到 SBPF memory 的 refinement；
- 完整 Agave verifier（上游 verifier 只覆盖 instruction-level version/divisor 条件）。

因此下一步若继续，不应扩大 Extract 语法；应先为现有 textual emitter 做同一小子集的
control-flow / instruction correspondence，再扩大 typed bridge。

## Tests

- `Tests/SolanalibSpec.lean`：上游 executable semantics 的 bounded characterization。
- `Tests/NormalizationSpec.lean`：真实抽出的 Counter checked write 通过 Core Place 和 SVM slot
  降成 `add64` body + `stxdw [r6 + 104], r4` typed fragment。
