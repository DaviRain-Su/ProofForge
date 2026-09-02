---
id: e-extpermit-001
scope: evm
status: done
depends-on: [e-permit-err-001]
---

# e-extpermit-001 Vault 封闭外部 permit CALL

## objective

Vault 对外部 token 发一条编译期固定的 EIP-2612 `permit` CALL。不是泛化 CALL。

- `evmTokenPermit token owner spender value deadline v r s`
- selector `0xd505accf`，calldata 228 字节
- CALL 失败 / 假返回 revert。返回数据按 ERC-20 bool 规则
- `Examples.Evm.Vault.permit`
- Anvil：对内部 Token 签 permit，Vault 代发后 allowance 指向 Vault
- SVM / Legacy adapter 拒新叶

## 不做

动态 selector；DAI 形 permit；泛化 CALL。
