---
id: e-domsep-001
scope: evm
status: done
depends-on: [e-ownimm-001]
---

# e-domsep-001 Token.DOMAIN_SEPARATOR view

## objective

`Examples.Token.DOMAIN_SEPARATOR()` 返回和 `permit` 同一份编译期固定 EIP-712 domain hash。

- 新增 `evmDomainSeparator : Bytes32`
- Yul：`keccak256(EIP712Domain || keccak("Token") || keccak("1") || chainid || address)`
- ABI 是 `bytes32`（width 33），不是 `uint256`
- Anvil：部署后 `DOMAIN_SEPARATOR()` 与 `cast` 算的 typed-data domain 一致；permit 后不变
- SVM / Legacy adapter 拒新叶

## 不做

可配置 name/version；把 domain 写进 storage；泛化 keccak 叶。
