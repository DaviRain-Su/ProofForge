---
id: e-comp-013
scope: evm
status: done
depends-on: [e-comp-012]
---

# e-comp-013 地址谓词 isZero20 / eqImm20

## objective

把现有合同里还散着的地址守卫收进 Source。Addr20 投影和 `eq20` 操作数共用
`unfoldUserHelpers`，不再各写一份有界 unfold。不新增 Ops / IR / 主 Emit case，
digest 不变。

WideWord：

- `zero20` / `isZero20` 替换 `eq20 a ⟨0,0,0⟩`
- `eqImm20` 替换 `eq20 a evmImm20`

合同：

- Token / Ownable 零地址守卫走 `isZero20`
- Ownable `bump` 走 `eqImm20`
- Token mint / burn / burnFrom 的零地址 LOG 走 `zero20`
- map debit/credit 写 combinator 仍不迁：会改 extracted IR

Extract：Addr20 投影、`eq20` 操作数、`addr20Leaves` / `uint256Leaves` 共用
`unfoldUserHelpers`，不再各写一份有界 unfold。

## 不做

把 Approval 的共享 `let next` 打进写 helper；环境 opcode Source；pause / mint；
拆 `asVal`。
