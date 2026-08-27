---
id: e-comp-012
scope: evm
status: done
depends-on: [e-comp-011]
---

# e-comp-012 HashedMap 源侧 revertInsufficient

## objective

Token 的 `Insufficient(have,want)` 不再手写 `revertInsufficient (get …)`。
`HashedMap.Source` 提供 `revertInsufficientAddr256` / `revertInsufficientPair256`。
`@[pf_inline]` 消去到已有 NativeFx revert 和 map get。不新增 Ops / IR / 主 Emit
case，digest 不变。

- Token `burn` / `burnFrom` / `transfer` / `transferFrom` / `decreaseAllowance`
  走这些 helper
- NativeFx 仍保留裸 `revertInsufficient held want`
- ClosedCall view（Vault `held` / `allowed`）已经是 Source，本切片不改

## 不做

把 `asVal` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
