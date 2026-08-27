---
id: e-comp-011
scope: evm
status: done
depends-on: [e-comp-010]
---

# e-comp-011 HashedMap 源侧 nextAdd / nextSub

## objective

Token 的余额/额度算术不再手写 `add256 (get …) amt`。`HashedMap.Source` 提供
编译期查询 `nextAddAddr256` / `nextSubAddr256` / `nextAddPair256` /
`nextSubPair256`。合同绑定一次 `next`，再交给 `set*` 和 LOG。`@[pf_inline]`
消去到已有 map get 和 WideWord arith。不新增 Ops / IR / 主 Emit case，digest
不变。

- Token `increaseAllowance` / `decreaseAllowance` / `burn` / `burnFrom` /
  `transfer` / `transferFrom` 走这些查询
- 比较仍走 `geAddr256` / `gePair256`
- 不把 get+arith+set 打成一个写 helper（会拆掉共享 `let`，digest 变）

## 不做

把 `asVal` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
