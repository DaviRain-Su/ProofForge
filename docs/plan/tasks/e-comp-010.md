---
id: e-comp-010
scope: evm
status: done
depends-on: [e-comp-009]
---

# e-comp-010 HashedMap 源侧 geAddr256 / gePair256

## objective

Token 的余额/额度比较不再手写 `ge256 (getAddr256 …)`。`HashedMap.Source`
提供编译期 combinator `geAddr256` / `gePair256`。`@[pf_inline]` 消去到已有
map get 和 WideWord `ge256`。不新增 Ops / IR / 主 Emit case，digest 不变。

- Token `burn` / `burnFrom` / `transfer` / `transferFrom` / `decreaseAllowance`
  走这些 combinator
- 直接 get/set 和 `get + arith + set` 写回仍用现有 Source
- 打包 credit/debit 写 combinator 会改 extracted IR（LOG 与 map set 的共享
  `let` 形状），暂不迁

## 不做

把 `asVal` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
