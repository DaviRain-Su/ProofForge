# ProofForge.Extract.LegacyOps (`ProofForge.Ops`)

## Purpose

旧抽取器从 elaborated `Expr` 抽出的封闭操作 union。该定义同时含有 SVM 和 EVM
叶子，仅由 `Extract` 兼容链路和 Golden fixtures 使用；新的抽取链路使用
`Core.Ops`、`Extract.IR` 以及各 target 自有的 `Svm.Ops` / `Evm.Ops`。

文件位于 `ProofForge/Extract/LegacyOps.lean`，暂时保留 `ProofForge.Ops` 命名空间，
避免破坏兼容 API。发射 overflow 路径的依据是 checked 算术，不是方法名。

## Types

`Val`：`arg` / `field` / `lit` / SVM 叶 `clock*` `signerKey0` `acc*` `findPda` `sha256Lit` `keccak256Lit` / EVM 叶 `evmCaller` `evmBlockNumber` `evmTimestamp` `evmChainId` `evmSelf` `evmCallValue` `evmSelfBalance` / Addr20 三叶 `evmCallerW*` `evmSelfW*` / 位运算 `bitAnd` `bitOr` `bitXor` `bitNot` `shiftL` `shiftR` / `indexGet` / `loopIx`

`Cmp`：`eq` / `ne` / `lt` / `le` / `gt` / `ge`

`Op`：checked 四则、`ite`、`invoke`（编译期 program/metas/data；`systemTransfer` 是特化）、EVM 效应、`forAccum` / `forBody` / `indexSet`、hashed Map / pair-key Map / 封闭 ERC-20、`evmLog`、`storeField` / `okState` / `errorOverflow` / `errorNamed` / `returnU64` / `returnState`

`storeField name v`：写一个已摊平的账户叶。mutate 槽 diff 一次可发多条；单叶仍压成 `okState`。

`forBody n body`：有界 `for i in [:n]`，体里可用 `loopIx`。体里 `exit` 的 op 提前结束。抽出器还不能正确区分循环 binder 和外层参数。

## Tests

`increment` 抽出 `checkedAddU64`；`scale`/`divide`/`modulo` 抽出对应 op；`wrapping*` fail closed。
