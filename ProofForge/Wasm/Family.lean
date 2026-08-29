import ProofForge.Extract.IR

/-!
# WASM 家族纪律

WASM 是一个**链家族**，不是一个 target。CosmWasm、Arbitrum Stylus、ink!、NEAR、
XRPL Bedrock 各自拥有不同的 host function、存储模型和入口 ABI；「一份 wasm 走天下」
不存在（见 `docs/research/06-wasm-feasibility.md` §四.4 与旧仓 proof_forge 的
`family-wasm-host.md` 禁 `GenericWasmHostPlan` 的先例）。

因此本仓的 WASM 支持按**每链一个 target**组织：

```text
ProofForge/Wasm/
  Family.lean     -- 本文件：家族级约定，不含任何链特化逻辑
  Xrpl/           -- 每条具体链一个子目录（Ops / IR / Emit / Registry / Assemble / Commands）
```

家族层**只**共享跨链必然成立的最小约定：

- 对 svm / evm 叶子的 fail-closed 投影拒绝（`rejectValKind` / `rejectOpExt`）；
- 语法约定：错误消息 `{target} rejects {svm|evm} {value|effect}`。

家族层**禁止**共享：Plan、target IR、emitter、digest 域、宿主合同。这些全部由
具体链子目录拥有；加第二条 WASM 链时新建 `Wasm/<Chain>/`，不横向修改既有链。
-/

namespace ProofForge.Wasm.Family

/-- Reject a foreign target value leaf on behalf of one named wasm-family chain. The
result type is the caller's chain dialect; the rejection happens before any chain
extension is consulted. -/
def rejectValKind (target : String) : Extract.IR.ValKind → Except String α
  | .svm _ => throw s!"extract/unsupported: {target} rejects svm value"
  | .evm _ => throw s!"extract/unsupported: {target} rejects evm value"

/-- Reject a foreign target effect on behalf of one named wasm-family chain. -/
def rejectOpExt {V : Type} {W : Type} (target : String)
    (payload : Extract.IR.OpExt V) : Except String W :=
  match payload with
  | .svm _ => throw s!"extract/unsupported: {target} rejects svm effect"
  | .evm _ => throw s!"extract/unsupported: {target} rejects evm effect"

end ProofForge.Wasm.Family