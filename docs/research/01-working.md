# Working Document: Lean 4 直写 Solana 合约

> Rounds 1–3 merge. Core question: 能否剥离 Solana，用普通 Lean 4 语法写合约、完整复用 Lean FV、经汇编/FFI 落到可部署程序？

## Dimension 1 — 语言面

- **D1-1**: PF 今日是自定义命令 `program Name where`。
  - Source: `proof_forge/ProofForgeV2/Language/Syntax.lean:20-234`, `ProgramElaborationV1.lean:3983-4013`
  - Examples: `Examples/TransferSol.lean:12-22`, `Examples/Accumulator.lean:7-20`, `Examples/Counter.lean:20-42`
- **D1-2**: ADR-0002 否决无约束 builder/StateM，不是否决一切普通 Lean 表面语法。
  - Source: `docs/adr/0002-unified-program-dsl.md:47-50`
- **D1-3**: PF 合约体禁止递归/无界循环/IO/Type/tactics/FFI。这是 DSL 限制。
  - Source: `docs/specs/type-effect-system.md:116-129`
- **D1-4**: 相邻 theorem 是普通 Lean；主语是 `SemanticProgramV1`。
  - Source: ADR-0027:61-95
- **D1-5**: 「不用新 DSL」三分：(a) 新具体语法；(b) 普通 Lean + attribute + 校验子集 — 可抽出；(c) 无约束 Lean — 不可。
  - Source: Lean 4.33.1 `Declaration.lean`, `MonadEnv.lean` `getConstInfo`
- **D1-6**: 抽出权威应是 elaborated `Expr` 闭包，不是 LCNF/IR。
- **D1-7**: kernel 不保证 opaque/sorry/extern/implemented_by/资源/ABI。
- **D1-8 (R3)**: 路径 B 的 attribute 只能是标记；`Solana.Contract` 必须是惰性数据，不能是无约束 host builder（否则退回 ADR-0002 否决案）。路径 B 在形式意义上仍是语言子集，只是表面语法是 Lean。

## Dimension 2 — 形式化验证复用

- **D2-1**: `InvariantTheoremV1` = 全体 conforming 状态上不变量为 true。
  - Source: `InvariantABI.lean:48-55`
- **D2-2**: `PreservationTheoremV1` = admission + 初态/init + 一步保持。
  - Source: `PreservationABI.lean:459-569`
- **D2-3**: Formal D1–D4 = 0/27。
  - Source: `MIGRATION_MATRIX.md:9-37`
- **D2-4**: 五层语义。用户定理默认层 1。
- **D2-5**: FV 对所选语义完全可复用；对 `.so` 需要 refinement。
- **D2-6**: 有界 kernel 证书：Reference→HandlerIR 若干 recipe；StateCell 四场景 HandlerIR↔`.s`；稀疏 step 证书 55/55/70/56。一般 lowering / ELF / SVM OPEN。
  - Source: `HandlerSemanticsV1`, `SbpfHandlerJoinV1`, `docs/plan/solana-adr-0048-next.md`
- **D2-7**: MiniAmmL1 HEAD 无 theorem；ADR-0034 GREEN 过时。
  - Evidence: `Examples/MiniAmmL1.lean:123-127`; `Tests/Semantic/MiniAmmL1Admit.lean` 只测 admission
- **D2-8 (R3)**: 部署行为 TCB 在 frontend 以下几乎相同。B 新增 subset checker + extractor；A 信任 decoder/Normalize。

## Dimension 3 — Lean 编译 / FFI / 抽取

- **D3-1**: Lean 4.33.1 无 extraction 命令。C 走 `LCNF.emitC`。
  - Verified: `lean --version` → 4.33.1 commit `819816b2e0a3`; `Shell.lean:559-572`
- **D3-2**: FFI = C ABI。官方 interface unstable。
  - URL: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
- **D3-3**: 生成 C `#include <lean/lean.h>` + `lean_alloc_ctor`/`lean_inc`。实证：`.lake/packages/assembler-semantics/.lake/build/ir/SbpfSemantics/Api.c`
- **D3-4**: EmitLLVM：「CI for LLVM is dysfunctional so this code is not actually tested.」
- **D3-5**: Solana Clang 编译生成 C：预期先死在缺 lean.h/runtime。[UNVERIFIED empirically]
- **D3-6**: 堆 32KiB 默认 / 256KiB 最大；每帧栈 4096B；调用深度 64。
  - URL: https://solana.com/docs/core/programs
- **D3-7**: 自定义 emitter 可挂钩 LCNF/IR 或 Lake facet；非稳定 API。
- **D3-8**: 「Lean FFI → 汇编 → Solana」不可行。根因：FFI 不是后端；宿主 runtime 非法；ISA 错误。

## Dimension 4 — Solana / sBPF 物化

- **D4-1**: `ValidatedSourceV1 → CompiledSemanticV1 → Plan → HandlerIR → .s → sbpf → .so`
  - Source: `ProductionPreparationV1.lean:60-200`, `FinalizeV1.lean:82-105`
- **D4-2**: `build/v2/solana-runtime/StateCell/StateCell.so` = ELF 64-bit eBPF, 1624B。只证格式。
- **D4-3**: sbpf 0.2.2 commit `d835bc6e638e4f55b88f31a31bbc92e3a2e0a5ba`
- **D4-4**: assembler-semantics `ef6e20c20827e4158e1cb025518465aa8beb46da`
- **D4-5**: 普通 Lean 可显式建模 AccountInfo；裸函数不自动带 ABI。
- **D4-6**: 无 platform-tools 产品路径。换汇编器 = 语义分叉。
- **D4-7 (R3)**: Finalize 后置条件只有进程成功 + 非空 ELF，不是正确性证明。`runtime-tests/solana/preflight/manifest.json:44` 称 locked-sbpf 为 same-host engineering evidence。
- **D4-8 (R3)**: CPI fixtures 明确 “Not a product artifact path.”（`SystemCpi.lean:11`）。v0 应排除通用 CPI/PDA。

## Dimension 5 — 剥离成本

- **D5-1**: Solana 56 files / 57,100 LOC；PF 342 / 272,193；minus other targets 232 / 171,661。
- **D5-2**: 直接非本目录 import 37。传递闭包 [UNVERIFIED exact]。
- **D5-3**: solana-client = 离线校验器。
- **D5-4**: 推荐依赖闭包提取，不是整仓减 target，也不是只拷 emitter。
- **D5-5 (R3)**: A 要 vendor Language/Source/Typed/Normalize/Semantic + Solana。B 不 vendor Syntax/Elaboration/Normalize，但要新写 checker+extractor；Solana lowering 两边都要。
- **D5-6 (R3)**: Materializer 含过渡 shim，剥离是 curated fork。

## Dimension 6 — 对照与失败模式

- **D6-1**: 可比系统几乎不把证明语言部署到链上（Certora/Kani/Move/Cairo+Lean/ConCert）。
- **D6-2**: 13 类失败模式。
- **D6-3**: PF ADR 本身是诚实清单。
- **D6-4**: 未发现成熟 Lean4→sBPF 生产编译器。[UNVERIFIED global negative]
- **D6-5**: Seahorse beta；Solang archived。
- **D6-6 (R3)**: 正确产品姿态是四种之一：规格与实现分离 / 验证生产语言 / 语言-VM 共设计 / 受限模型 + 显式编译关系。用户原方案是第五种失败式：「kernel-check + 随便一个后端 = 部署证明」。

## Architecture (R3)

### Path A — reuse PF DSL

```
program where → PF decoder → ValidatedSourceV1 → Check/Normalize
  → SemanticProgramV1 (+ Lean theorems on Reference)
  → Solana Plan → HandlerIR → emitSbpfAsmV1 → .s → locked sbpf → .so
```

### Path B — ordinary Lean subset

```
@[solana_entry] def … → elaborator → Expr closure
  → NEW fail-closed subset checker → NEW extractor → same Solana IR
  → emitSbpfAsmV1 → .s → locked sbpf → .so
```

### v0 IN / OUT

IN: 单账户、UInt8/32/64、条件、checked 算术、init/entry/view、Reference 定理、locked sbpf、Mollusk smoke。诚实声明不含 .so refinement。

OUT: 其它链、FFI-to-asm、无约束 Lean、.so 精化声明、通用 CPI/PDA、多可变账户、token/ATA。

## TCB (R3)

部署行为 TCB 两边几乎同：kernel + elaborator + (A: decoder/Normalize | B: checker/extractor) + materializer + emitter + sbpf + loader + SVM。

弱声明「kernel 接受了关于所选语义的定理」只需 kernel + 主语绑定正确。

## Recommendation (R3)

- 优先「写起来像 Lean、不要自定义关键字」→ B
- 优先「尽快出可编译的已验证 Solana 程序」→ A
- 两边都立刻要 → 先 A，B 作为第二前端，对同一 semantic IR 做差分验证

成本：3/6 月 A 明显便宜；12 月仅当普通 Lean UX 是长期差异化时 B 才可能更便宜。

## Killers (R3)

1. B 的传递闭包不能 fail-closed
2. 证明主语与编译主语不是同一 semantic identity
3. emitter 静默降级/丢指令
4. 账户 ABI/别名/写回未定义
5. sbpf ELF 不被目标 loader 接受
6. 干系人把 .so refinement 当 v0 必达
7. 通用 CPI/PDA 当 v0 必达
8. 无法冻结/策展上游 PF
9. 没有对抗性 SVM 回归环境

## Conflicts resolved

- ADR-0032 proposed vs sole rail：以代码为准
- ADR-0034 MiniAmmL1 GREEN：HEAD 无 theorem

## Verdict

| 用户原话 | 判定 | 根因 |
|---|---|---|
| 剥离 Solana 独立仓 | 有条件可行 | 依赖闭包大，但是 curated fork 可做 |
| Lean 4 语法、不新设计合约语言 | 有条件可行（路径 b） | 不是路径 c；子集仍是形式语言 |
| 完全复用 Lean FV | 对所选语义可行；对 .so 不可（当前） | 缺 refinement 链；formal 0/27 |
| Lean FFI → 汇编 → 合约 | 不可行 | FFI≠后端；runtime 非法；ISA 错 |
