# ProofForge.Assemble

## Purpose

调用本机 `sbpf 0.2.2`，把 Counter 汇编变成 ELF `.so`。

## Boundary

子进程，不是 FFI。按 `Program.name` 写 `src/Name/Name.s`，递归找 `Name.so`（`sbpf` 会嵌套 `deploy`）。

## API

- `assembleProgram outDir program : IO Result`
- `assembleCounter` = `assembleProgram` 的别名
- `pfAssemble` 遍历 `Golden.programs`
- `lake exe pfAssemble -- build/sbpf`（写出 Counter.so 与 Pair.so）

## Tests

`runtime-tests/solana` Mollusk：Counter 4/4；Pair init / creditLeft 保 right / getLeft / overflow。
