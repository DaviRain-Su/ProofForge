---
id: e-permit-001
scope: evm
status: done
depends-on: [e-swap3-001]
---

# e-permit-001 封闭 EIP-2612 形 `permit`

## objective

给 `Examples.Evm.Token` 一条编译期固定的 `permit(owner,spender,value,deadline,v,r,s)`。
不是泛化 `ecrecover` API，也不是外部 token CALL。

- 新增 `Bytes32`（ABI `bytes32`，width 33）和 `evmPermit`
- Yul：deadline ≥ timestamp；hashed nonce[owner]；EIP-712 digest（name=`Token`，version=`1`，chainid，address）；`ecrecover`；写 allowance；nonce++；LOG3 Approval
- 过期 → `Expired()`；签名失败 → revert / `Unauthorized`
- `nonceOf(address)` view
- SVM / Legacy adapter 拒新叶
- Anvil：typed-data 签名后 permit，再 transferFrom

## 不做

可配置 name/version；EIP-2612 全套错误；泛化 keccak/ecrecover 叶；DAI 形 permit；Ownable.owner 改 immutable。
