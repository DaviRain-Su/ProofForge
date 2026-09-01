# ProofForge.Svm.SemanticsBridge

## Purpose

Bridge ProofForge SVM emit (`.s` text) into the pinned `sbpfSemantics`
(assembler-semantics) L2 program model, then small-step under `runFuel`.

This is the engineering entry for **L3/E2** (`svm-sem-002`): a repeatable
emit → parse → step observation gate. It does **not** prove kernel
correspondence (that is E3+).

## Pipeline

```text
Extract / Golden IR
  → Svm.Emit.emitCounterAsm / emitAsm
  → SemanticsBridge.assembleSf
  → SbpfSemantics.Program
  → runSfInitial? / runSfNext?
  → Observation (r0, returnData, …)
```

## Main API

| Symbol | Role |
|---|---|
| `assembleSf` | Parse emitted `.s` into `SbpfSemantics.Program` |
| `SfIx` | Instruction bytes + account data for one call |
| `runSfInitial?` | Fresh machine: assemble + load input + `runFuel` |
| `runSfNext?` | Rewrite ix on shared memory, then `readyForNext` + `runFuel` |
| `sfInput?` / `pokeIx?` | Loader-shaped input region / ix rewrite |

## Corpus gate (E2)

`Tests/SemanticsSpec.lean` pins:

1. **Counter** — parse band + `initialize → increment → get` observation sequence +
   unknown-discriminator fail-closed
2. **Window** — two-cell container: `initialize → setTail → getHead` (head unchanged)
3. **Named parse sweep** — every Golden program that emits successfully must parse;
   failures report the program name

CI already builds `Tests.SemanticsSpec` in the Lean lane (`svm-eng-001`).

## Non-goals

- Solanalib CFG correspondence (`svm-sem-003`)
- `AccountWords` ↔ `storev` (`svm-sem-004`)
- Full container proofs (`svm-sem-005`)
- ELF / Loader / CPI / host adequacy
- Dumping every Registry program as a step golden
