---
id: e-comp-009
scope: evm
status: done
depends-on: [e-comp-008]
---

# e-comp-009 WideWord 源侧 limb 查询

## objective

`UInt256` state 写回不再投影 `UInt256.wN (add256/sub256 …)`。`WideWord.Source` 提供
编译期 limb 读 `addW0..W3` / `subW*` / `mulW*`，以及由这些叶组成的 `add` / `sub` /
`mul` ctor helper。Extract 展开 `@[pf_inline]` 后落到已有 `evmAdd256` 投影，不新增
Ops / IR / 主 Emit case，digest 不变。

- Token `supply` 写回走 `WideWord.Source.add` / `sub`
- Wide 的返回路径仍用 `add256` / `sub256` / `mul256`
- `asVal` / `uint256Leaves` 对 Source helper 做有界 unfold

## 不做

把 `asVal` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
