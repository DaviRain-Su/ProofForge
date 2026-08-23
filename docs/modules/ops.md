# ProofForge.Ops

## Purpose

从 elaborated `Expr` 抽出的操作。发射 overflow 路径的依据是 checked 算术，不是方法名。

## Types

`Val`：`arg` / `field` / `lit` / SVM 叶 `clock*` `signerKey0` `acc*` `findPda` `sha256Lit` `keccak256Lit` / EVM 叶 `evmCaller` `evmBlockNumber` `evmTimestamp` `evmChainId` `evmSelf` `evmCallValue` `evmSelfBalance` / Addr20 三叶 `evmCallerW*` `evmSelfW*` / 位运算 `bitAnd` `bitOr` `bitXor` `bitNot` `shiftL` `shiftR` / `indexGet` / `loopIx`

`Cmp`：`eq` / `ne` / `lt` / `le` / `gt` / `ge`

`Op`：checked 四则、`ite`、`invoke`（编译期 program/metas/data；`systemTransfer` 是特化）、EVM 效应、`forAccum` / `forBody` / `indexSet`、hashed Map / pair-key Map / 封闭 ERC-20、`evmLog`、`okState` / `errorOverflow` / `errorNamed` / `returnU64` / `returnState`

`forBody n body`：有界 `for i in [:n]`，体里可用 `loopIx`。体里 `exit` 的 op 提前结束。抽出器还不能正确区分循环 binder 和外层参数。

## Tests

`increment` 抽出 `checkedAddU64`；`scale`/`divide`/`modulo` 抽出对应 op；`wrapping*` fail closed。
