import ProofForge.Extract.IR

/-!
# WASM 家族纪律

WASM 是一个**链家族**，不是一个 target。CosmWasm、Arbitrum Stylus、ink!、NEAR、
ICP、XRPL Bedrock 都编译到 wasm 字节，但各自的 **host function（runtime）** 和
**存储布局**不同；不存在通用 wasmtime 宿主，也不存在「一份 wasm 走天下」
（见 `docs/research/06-wasm-feasibility.md` §四.4）。

产物是 **`.wasm`**。Lean 直接 lowering 到 WAT / wasm，不经过 rustc，也不把
Rust 源当 artifact。Rust 生态的 `cargo` / `xrpl-wasm-std` 是链侧开发者工具，
不是 ProofForge 的 Tool Lock。

```text
ProofForge/Wasm/
  Family.lean     -- 外来叶子 fail-closed 拒绝
  Host.lean       -- 链间差异的注入面：host import 表 + 存储布局 + 入口 ABI
  IR.lean         -- 家族共享：程序形状、v0 子集、canonical 拼写（域由链注入）
  Emit.lean       -- 家族共享：Core → WAT（host contract 注入 import / 存储）
  Xrpl/           -- 每条具体链一个子目录
```

家族层共享：

- 对 svm / evm 叶子的 fail-closed 投影拒绝（`rejectValKind` / `rejectOpExt`）；
- Core 标量与控制流到 WAT 的 lowering（`i64` 算术、`if`、locals）。

家族层**禁止**共享：Plan、digest 域、host import 表、存储布局。这四样由
`Wasm/<Chain>/Host` 拥有。加第二条链时新建 `Wasm/<Chain>/`，不横向修改既有链。
-/

namespace ProofForge.Wasm.Family

/-- Reject a foreign target value leaf on behalf of one named wasm-family chain. The
result type is the caller's chain dialect; the rejection happens before any chain
extension is consulted. -/
def rejectValKind (target : String) : Extract.IR.ValKind → Except String α
  | .svm _ => throw s!"extract/unsupported: {target} rejects svm value"
  | .evm _ => throw s!"extract/unsupported: {target} rejects evm value"
  | .xrpl _ => throw s!"extract/unsupported: {target} rejects xrpl value"

/-- Reject a foreign target effect on behalf of one named wasm-family chain. -/
def rejectOpExt {V : Type} {W : Type} (target : String)
    (payload : Extract.IR.OpExt V) : Except String W :=
  match payload with
  | .svm _ => throw s!"extract/unsupported: {target} rejects svm effect"
  | .evm _ => throw s!"extract/unsupported: {target} rejects evm effect"
  | .xrpl _ => throw s!"extract/unsupported: {target} rejects xrpl effect"

end ProofForge.Wasm.Family
