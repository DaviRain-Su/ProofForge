# SolanaLean.Ops

## Purpose

从 elaborated `Expr` 抽出的操作。发射 overflow 路径的依据是 checked 算术，不是方法名。

## Types

`Val`：`arg` / `field` / `lit` / `clockSlot` / `signerKey0` / `accLamports0` / `accOwner0` / `accDataLen0` / `accN` / `isSigner0` / `isWritable0` / `isExecutable0`

`Cmp`：`eq` / `ne` / `lt` / `le` / `gt` / `ge`

`Op`：checked 四则、`ite`、`invoke`（编译期 program/metas/data）、`okState` / `errorOverflow` / `returnU64` / `returnState`。`systemTransfer` 是 `invoke` 特化。

## Tests

`increment` 抽出 `checkedAddU64`；`scale`/`divide`/`modulo` 抽出对应 op；`wrapping*` fail closed。
