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
  Family.lean     -- 本文件：外来叶子 fail-closed 拒绝
  Host.lean       -- 链间差异的注入面（存储 / host import / 入口 ABI）
  IR.lean         -- 家族共享：程序形状、v0 子集、canonical 拼写（域由链注入）
  Emit.lean       -- 家族共享：Core → Rust 发射（host contract 注入链特化文本）
  Xrpl/           -- 每条具体链一个子目录
```

家族层共享且仅共享跨链必然成立的约定：

- 对 svm / evm 叶子的 fail-closed 投影拒绝（`rejectValKind` / `rejectOpExt`）；
- 语法约定：错误消息 `{target} rejects {svm|evm} {value|effect}`；
- 经 Rust 编译到 wasm 的链所共用的 Core→Rust 程序形状、v0 子集检查、
  canonical 拼写和发射器（`Wasm.IR` / `Wasm.Emit`）。

家族层**禁止**共享：Plan、digest 域字符串、宿主合同实例。这三样由
`Wasm/<Chain>/` 拥有（`Host.contract` 注入发射器；digest 域例如 `xrpl-bedrock|`）。
加第二条 WASM 链时新建 `Wasm/<Chain>/`，不横向修改既有链的方言 / Host / Registry。
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
