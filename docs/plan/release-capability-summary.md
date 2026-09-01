# Release capability summary (fail-closed)

Short ceiling for GitHub Release notes. Full matrix:
[capability-matrix.md](capability-matrix.md).

## Shared

- `@[pf_entry]` programs with fixed scalar shapes; recursive / unbounded data fail closed.
- Checked `UInt*` arithmetic and Core math/codec bounded frames.
- Host `Array` / open recursion rejected at extract.

## SVM (`ProofForge.Svm.Sdk`)

- Account bytes + typed Sdk handles; Runtime/Source available for `pf_inline` erase.
- **Not** in the SDK import surface: `Emit` / `Assemble` / `Registry` / Examples.

## EVM (`ProofForge.Evm.Sdk`)

- Static slots + hashed typed namespaces via Sdk facades.
- **Not** in the SDK import surface: `Emit` / `Assemble` / `Registry` / Examples.

## CLI

- `pf build --module` / `pf.toml` `[[program]]` for user modules.
- Bare names still map to in-repo `Examples.*` fixtures (compiler regression only).
- `pf init <name> --target svm|evm` copies Sdk-only templates.
