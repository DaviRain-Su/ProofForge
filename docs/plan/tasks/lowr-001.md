---
id: lowr-001
scope: lower
status: done
depends-on: [extr-001]
---

# lowr-001 接 ProofForge 发射器

## objective

发射与 PF StateCell 对齐的 sBPF `.s` 文本。PF 的 `IR` 是私有构造，本刀不 import 16 万行 PF；布局/disc/overflow 与黄金 `StateCell.s` 对齐。

## context

docs/02-architecture.md；PF EmitIRV1 / EmitSbpfAsmV1

## path

ProofForge/Lower.lean；lakefile 对 proof_forge 的 path/git pin

## verification

生成的 `.s` 含 entrypoint 与 checked-add 控制流；非法 IR 不发射。
