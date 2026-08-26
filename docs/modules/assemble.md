# ProofForge.Svm.Assemble

## Purpose

调用本机 `sbpf 0.2.2`，把 Counter 汇编变成 ELF `.so`。

## Boundary

子进程，不是 FFI。按 `Program.name` 写 `src/Name/Name.s`，递归找 `Name.so`（`sbpf` 会嵌套 `deploy`）。
读取 ELF 后、写最终 `.s` / `.so` / IDL 前执行 Loader-v3 size gate：Agave 4.0 的
`ProgramData` account 上限 10 MiB，其中 metadata 45 bytes，因此 ELF 最大
10,485,715 bytes。边界值由 `loaderV3SizeEligible` 的正反测试固定；超限以
`assemble/size` fail closed。该纯函数门本身只声明 Loader-v3 **体积可容纳**；独立的
`runtime-tests/surfpool/smoke.sh` 会关闭 instant direct-state 路径，通过 Surfpool 1.5.0
执行真实 Loader-v3 buffer/write/deploy/authority transactions。该本地门不等同于公网部署。

## API

- `assembleIRProgram outDir program : IO Result`（正常 target IR 路径）
- `assembleProgram` / `assembleCounter`（旧 extraction IR 兼容入口）
- `loaderV3MaxElfBytes` / `loaderV3SizeEligible`
- `pfAssemble` 遍历 `Golden.programs`
- `lake exe pfAssemble -- build/sbpf`（写出 Counter.so 与 Pair.so）

## Tests

`runtime-tests/solana` Mollusk：Counter 4/4；Pair init / creditLeft 保 right / getLeft / overflow。
`runtime-tests/surfpool/smoke.sh`：Phoenix ELF 本地 Loader-v3 交易部署、confirmed deploy
signature、Program/ProgramData owner/layout 和完整 ELF bytes 一致性。
