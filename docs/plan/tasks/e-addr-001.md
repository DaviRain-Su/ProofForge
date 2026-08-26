---
id: e-addr-001
scope: evm
status: done
depends-on: [e-tok-001]
---

# e-addr-001 Addr20 一等类型 + ABI address

## objective

E-ADDR 整包。把三叶 `w0 w1 w2` 收成 `ProofForge.Evm.Runtime.Addr20`，ABI 编成一个 `address`。IR / storage / hashed Map 仍摊三叶。

- `structure Addr20 where w0 w1 w2 : UInt64`（w2 只低 4 字节）
- `evmCaller20` / `evmSelf20` 返回 `Addr20`
- Runtime 菜谱改成 `Addr20` 参数：`evmSendEth`、`evmMapGetAddr`/`SetAddr`、pair map、`evmTokenTransfer`、`evmTokenBalanceOfSelf`
- 抽出：`Addr20` 参数 `paramWidths = 20`；返回 `retWidths = #[20]`、`retCount = 3`
- Yul：calldata 一个 word；`.field arg "w0/w1/w2"` 从该 word 拆叶；返回三叶再 pack 成 `address`
- 例子：Ownable / Token / Vault / TipJar 不再手拆三元组
- SVM 仍拒全部 EVM 叶
- Anvil：`cast` 走 `address` 参数

## 不做

嵌套 `Option Addr20`；动态 `address[]`；整值 `Addr20 = Addr20` 合成比较（身份比继续走三叶）；标准 `Transfer(address,address,uint256)`（E-LOG）。
