# SolanaLean.Ops

## Purpose

从 elaborated `Expr` 抽出的操作。发射 overflow 路径的依据是 checked 算术，不是方法名。

## Types

`Val`：`arg` / `field` / `lit` / SVM 叶 `clockSlot` `signerKey0` / EVM 叶 `evmCaller` `evmBlockNumber` `evmTimestamp` `evmChainId` `evmSelf` `evmCallValue` `evmSelfBalance` / Addr20 三叶 `evmCallerW*` `evmSelfW*` / 位运算 `bitAnd` `bitOr` `bitXor` `bitNot` `shiftL` `shiftR` / `indexGet` / `loopIx`

`Cmp`：`eq` / `ne` / `lt` / `le` / `gt` / `ge`

`Op`：checked 四则、`ite`、`systemTransfer`、EVM 效应、`forAccum` / `indexSet`、hashed Map / 封闭 ERC-20、`okState` / `errorOverflow` / `errorNamed` / `returnU64` / `returnState`

## Tests

`increment` 抽出 `checkedAddU64`；`scale`/`divide`/`modulo` 抽出对应 op；`wrapping*` fail closed。
