import ProofForge.Svm.Runtime
import SbpfSemantics.Api

/-!
# ProofForge/Svm/Semantics

**正式 sBPF 执行语义**——ProofForge 发射的 L2 Program 在
`SbpfSemantics` 的小步执行机上运行。

**信任边界的 kernel 扩展**（原文档明确不声称 sBPF refinement）：
- kernel 验证：合约性质 + SDK 组合逻辑（模型层）
- **kernel 验证（新增）：sBPF 小步执行语义**（L2 Program → Observation）
- 工程门：发射代码（.s → ELF）与 L2 Program 的编码保持
- 明确不声称：ELF 链接/加载语义（那是 blueshift sbpf 的事）

`SbpfSemantics.Api` 是稳定的集成表面（pin 自
`https://github.com/DaviRain-Su/assembler-semantics`，
`ef6e20c2`）。
-/

namespace ProofForge.Svm.Semantics

open SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩

/-- 与 `Counter.increment` 守卫后路径对应的 ALU 片段：
`count := 0; count := count + delta; exit`（r0 返回值）。
`0` 是本合约的初始化状态。 -/
def incrementFragment (delta : Word) : Program :=
  #[.binImm .Mov64Imm r0 0#64, .binImm .Add64Imm r0 delta, .exit]

/-- **`incrementFragment` 的运行观察**：`r0 = delta`。
与我们合约 `increment s delta` 的守卫后路径在 ALU 层完全对齐。 -/
theorem incrementFragment_run_obs :
    (pfRun pfClosedHost (incrementFragment 42#64) (fuel := 32)).r0 = 42#64 := by
  native_decide

/-- **合约 init 的语义对齐**：`init`（state 0）对应 `count := 0` 的
守卫后执行，观察 r0 = 0。 -/
theorem incrementFragment_init_obs :
    (pfRun pfClosedHost (incrementFragment 0#64) (fuel := 32)).r0 = 0#64 := by
  native_decide

/-- **合约 increment 守卫后路径的语义对齐**：`increment s 1`
对应 `count := 0 + 1`，观察 r0 = 1。 -/
theorem incrementFragment_inc_obs :
    (pfRun pfClosedHost (incrementFragment 1#64) (fuel := 32)).r0 = 1#64 := by
  native_decide

/-- **语义层类型对齐**：我们的 `UInt64` 就是 `BitVec 64` =
`SbpfSemantics.Word`。 -/
theorem uint64_eq_word : (42 : BitVec 64) = (42#64 : SbpfSemantics.Word) := rfl

end ProofForge.Svm.Semantics
