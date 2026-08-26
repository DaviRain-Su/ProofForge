---
id: e-supply-001
scope: evm
status: done
depends-on: [e-imm2-001]
---

# e-supply-001 Token.totalSupply 作为 UInt256 状态字段

## objective

Token 第一次把 `UInt256` 放进账户，而不是只当 ABI / hashed map payload。

- `State.supply : UInt256` 摊成 `supply_w0..w3`
- `mint` 用 `evmAdd256` 累加；`transfer` / `transferFrom` 不动它
- `totalSupply` view 读该字段，ABI `uint256`
- Anvil：mint 后总量等于铸出额；transfer 后总量不变
- SVM / Legacy adapter 不新增叶

## 不做

burn；cap；把余额也改成账户字段；泛化 UInt256 DSL。
