# SolanaLean.Assemble

## Purpose

调用本机 `sbpf 0.2.2`，把 Counter 汇编变成 ELF `.so`。

## Boundary

子进程，不是 FFI。在工程目录里递归找 `Counter.so`（`sbpf` 会嵌套 `deploy`）。

## API

- `assembleCounter outDir : IO Result`
- `lake exe solanaLeanAssemble -- build/sbpf`

## Tests

`runtime-tests/solana` Mollusk：init / increment / get / overflow 保持。
