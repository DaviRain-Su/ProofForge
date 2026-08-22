# Dimension 6 audit — comparison and failure modes (Round 4)

Date: 2026-08-22. The numbering below makes D6-2 auditable. Items 1–9 preserve the
Round-3 `Killers` order in [`01-working.md`](01-working.md); items 10–13 reconstruct the
remaining failure classes from that document's D3/D4 findings and ProofForge's normative
rejections/non-claims. They are failure modes, not claims that every compared system has failed.

## 13 failure modes

1. **The accepted-language closure is not fail-closed.** An ordinary-Lean frontend accepts an
   unchecked transitive constant, recursion, `opaque`, `extern`, `implemented_by`, `unsafe`, IO,
   or host computation, so extraction is incomplete or differs by environment. ProofForge rejects
   arbitrary host builders for exactly this reason: `proof_forge/docs/adr/0002-unified-program-dsl.md:47-50`;
   Kani likewise documents that not all Rust features are supported:
   <https://model-checking.github.io/kani/>.
2. **The proved subject and compiled subject are not the same semantic identity.** A theorem is
   true of a model/AST while a decoder, normalizer, compiler, or stale `.olean` supplies another
   program. ProofForge therefore requires exact program, ordinal, canonical bytes, and semantic
   hash: `proof_forge/docs/adr/0034-preservation-abi.md` (D2). Move Prover avoids a source-only
   claim by analysing compiled Move bytecode: <https://www-cs.stanford.edu/~yoniz/cav20.pdf>.
3. **The emitter silently drops, rewrites, or substitutes unsupported operations.** A successful
   build then establishes neither rejection nor semantic preservation. ProofForge requires exact
   production `.s` bytes, strict parse/resolve, and fail-closed unknown instructions/directives:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md` (D2).
4. **Account ABI, aliasing, ownership, or write-back is underspecified.** A pure state theorem does
   not determine Loader account bytes, mutable alias rules, rollback, or returned data. ProofForge
   explicitly makes Loader V3 serialization its adapter obligation and excludes multi-account:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:104-115`; Solana's program
   constraints are documented at <https://solana.com/docs/core/programs>.
5. **The ELF is well-formed/nonempty but rejected or behaves differently in the target loader.**
   Linker, relocation, verifier, loader, and SVM semantics remain outside an ISA trace. ProofForge
   says ELF/linker/loader/SVM correctness is unproved:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:136-145`.
6. **A bounded/model proof is marketed as end-to-end `.so` refinement.** ProofForge permits only a
   bounded HandlerIR→resolved-sBPF observation claim, not `.so`/validator/runtime verification:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:145-149`; Cairo's project
   similarly states precisely that Lean formalizes CPU/VM semantics and AIR soundness:
   <https://github.com/starkware-libs/formal-proofs>.
7. **CPI, PDA, sysvars, crypto, dynamic loader behavior, or multiple accounts are promoted into v0
   without semantics and tests.** ProofForge's first slice makes these unsupported/fail-closed:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:104-116`.
8. **The upstream compiler/semantics dependency cannot be pinned and curated.** Branch/tag drift,
   ambient checkouts, runtime fallback, or API drift changes the theorem's subject. ProofForge
   requires a 40-character revision and forbids these fallbacks:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:40-61`.
9. **There is no adversarial target-runtime regression environment.** Kernel proofs alone do not
   expose loader-version, malformed-input, syscall, compute, or rollback mismatches. ProofForge
   explicitly does not upgrade Mollusk observations to a formal milestone:
   `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:17-22`.
10. **FFI is mistaken for a target backend.** Lean's FFI is a C-compatible native interoperability
    boundary, not an sBPF code generator; generated native code also assumes Lean's runtime:
    <https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/> and
    `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:63-75`.
11. **Host runtime/resource assumptions do not fit Solana.** GC/allocation, native ISA, stack frames,
    call depth, and heap assumptions can invalidate otherwise valid Lean execution. Solana records
    program resource limits at <https://solana.com/docs/core/programs>; the need for a target-owned
    lowering rather than provider-as-materializer is explicit in
    `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md:27-37`.
12. **Verification is vacuous, partial, or overgeneralized.** An implication can pass because
    admission failed; a `holds` theorem can be confused with initialization/reachability/step
    preservation; one example can be advertised as all contracts. ProofForge requires positive
    admission and a distinct preservation proposition and forbids “arbitrary contract” maturity
    claims: `proof_forge/docs/adr/0034-preservation-abi.md` (Background, D0–D3).
13. **Prototype or abandoned compiler status is hidden behind “it compiles.”** Seahorse explicitly
    says beta, incomplete, and not production-ready: <https://github.com/ameliatastic/seahorse-lang>;
    LF Decentralized Trust says Solang is archived:
    <https://www.lfdecentralizedtrust.org/projects/solang>. Neither status proves semantic failure,
    but both defeat an unsupported production-readiness inference.

## Compact comparison

| System | Implementation / proof subject | Deployment relation and relevant boundary | Primary source |
|---|---|---|---|
| Certora CVL | Separate CVL rules/invariants specify contracts; prover checks the contract against them | Verifies production contract/bytecode rather than compiling CVL into a contract | <https://docs.certora.com/en/latest/docs/cvl/overview.html> |
| Kani | Bit-precise model checking of Rust proof harnesses; safety, panic, overflow, assertions/contracts | Verifies Rust code; may exhaust resources and does not support every Rust feature (e.g. concurrency); it is not a new deployment language | <https://model-checking.github.io/kani/> |
| Move Prover | Move source plus specifications; source compiles to Move bytecode, then stackless bytecode/Boogie/SMT is checked | Language and VM are co-designed; prover analyses executable-language bytecode rather than compiling the proof language onto an unrelated VM | <https://www-cs.stanford.edu/~yoniz/cav20.pdf>, <https://aptos.dev/build/smart-contracts/prover> |
| Cairo formal-proofs / Lean | Lean specifications/proofs of Cairo CPU/VM semantics, program soundness/completeness, and AIR soundness | Lean checks claims about Cairo artifacts; the repository does not present Lean as the Cairo deployment compiler | <https://github.com/starkware-libs/formal-proofs> |
| ConCert | Smart contracts and execution model in Rocq/Coq, with verified embedding/testing and an extraction pipeline | Explicit extraction to supported targets (Liquidity, CameLIGO, Elm, Rust), making the compilation relation a first-class component | <https://github.com/AU-COBRA/ConCert> |
| Seahorse (beta) | Python-like source is cleaned/compiled to intermediate Rust and built through Anchor | Real Solana route, but its own README says beta, incomplete, and not production-ready | <https://github.com/ameliatastic/seahorse-lang> |
| Solang (archived) | Solidity compiler using LLVM for Solana and other targets | Was a direct production-language compiler route; project owner now labels it archived | <https://www.lfdecentralizedtrust.org/projects/solang>, <https://github.com/hyperledger-solang/solang> |
| ProofForge ADR-0002 / 0034 / 0048 | Checked DSL/source identity; separate exact-subject `holds` and `preserving`; bounded Reference→HandlerIR→resolved-sBPF certificates | Rejects unconstrained builders; four StateCell traces are 55/55/70/56 steps; explicitly leaves ELF/loader/SVM unproved | `proof_forge/docs/adr/0002-unified-program-dsl.md:47-50`; `proof_forge/docs/adr/0034-preservation-abi.md`; `proof_forge/docs/adr/0048-optional-solana-sbpf-semantics-provider.md`; `proof_forge/docs/plan/solana-adr-0048-next.md:18-35` |

## Search record

Search date: **2026-08-22**. Result is deliberately scoped: **no primary production
Lean→sBPF compiler was found in these searches**; this is not a global nonexistence claim.

- Web query group: `Certora CVL Kani Move Prover`; `Cairo Lean formal proofs ConCert`;
  `Seahorse beta Solang archived`.
- Web query group: `site:model-checking.github.io/kani verification`; `Move Prover official
  specification bytecode`; `ConCert Seahorse beta Solang archived`.
- Web query group: `github ConCert smart contracts extraction`; `github Seahorse Solana beta`;
  `github hyperledger solang archived`.
- Direct primary-page checks: `docs.certora.com/en/latest/docs/cvl/overview.html`,
  `model-checking.github.io/kani/`, `aptos.dev/build/smart-contracts/prover`,
  `github.com/starkware-libs/formal-proofs`, `github.com/AU-COBRA/ConCert`,
  `github.com/ameliatastic/seahorse-lang`, `lfdecentralizedtrust.org/projects/solang`.
- Local primary-source search/read: `proof_forge/docs/adr/0002-unified-program-dsl.md`,
  `0034-preservation-abi.md`, `0048-optional-solana-sbpf-semantics-provider.md`, and
  `proof_forge/docs/plan/solana-adr-0048-next.md`.
