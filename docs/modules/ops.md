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

`forBody n body`：有界 `for i in [:n]`，体里可用 `loopIx`。普通 early-return loop 和
显式 state-carrying fold 分开解码；callback-local index 会重写成 `loopIx`，外层方法
参数和 payload 保持原参数身份。Phoenix 的 17 / 19-phase fold 覆盖了跨迭代
state、动态 Vector 写和循环后的 continuation。

## Tests

`increment` 抽出 `checkedAddU64`；`scale`/`divide`/`modulo` 抽出对应 op；`wrapping*` fail closed。
