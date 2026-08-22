---
id: lowr-001
scope: lower
status: pending
depends-on: [extr-001]
---

# lowr-001 接 ProofForge 发射器

## objective

把本仓 IR 填进 PF HandlerIR，调用 `emitSbpfAsmV1` 得到 `.s`。

## context

docs/02-architecture.md；PF EmitIRV1 / EmitSbpfAsmV1

## path

SolanaLean/Lower.lean；lakefile 对 proof_forge 的 path/git pin

## verification

生成的 `.s` 含 entrypoint 与 checked-add 控制流；非法 IR 不发射。
