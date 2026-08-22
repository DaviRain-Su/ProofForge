---
id: extr-001
scope: extract
status: done
depends-on: [prof-001]
---

# extr-001 从 Expr 抽出 IR

## objective

读取 `increment` / `init` / `get` 的 elaborated `Expr`，抽出 `IR.Program`，与手工夹具 `BEq`。

## context

docs/02-architecture.md, docs/03-technical-spec.md

## path

ProofForge/Extract.lean, Tests/ExtractSpec.lean

## verification

抽出成功；改函数体导致 mismatch；禁止形状 fail closed。
