---
id: e-permit-err-001
scope: evm
status: done
depends-on: [e-domsep-001]
---

# e-permit-err-001 permit 验签失败改 Unauthorized(recovered)

## objective

`permit` 里 `ecrecover != owner` 不再裸 `revert(0,0)`，改成 ABI `Unauthorized(recovered)`。

- Yul：`staticcall` 失败或 recovered=0 仍 `revert(0,0)`
- recovered ≠ owner → `Unauthorized(recovered)`，36 字节
- Token ABI 列出 `Unauthorized(address)`
- Anvil：错签名 decode 出 Unauthorized

## 不做

把 ecrecover 失败也包装成 Unauthorized(0)；泛化 error DSL。
