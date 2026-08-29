import ProofForge.Svm.Sdk.Account
import ProofForge.Svm.Sdk.Pubkey
import ProofForge.Svm.Sdk.Program
import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.Queue
import ProofForge.Svm.Sdk.Pda
import ProofForge.Svm.Sdk.System
import ProofForge.Svm.Sdk.Token
import ProofForge.Svm.Sdk.AssociatedToken
import ProofForge.Svm.Sdk.Memo
import ProofForge.Svm.Sdk.Transient
import ProofForge.Svm.Sdk.Memory

/-!
# ProofForge SVM SDK

Source-facing facade for reusable SVM components. Applications describe fixed account geometry
once, then compose persistent POD fields, bounded vectors, ordered maps, allocators, FIFO
queues, and invocation-local transient buffers without defining protocol-specific operations
or emitter cases.

All persistent state remains inside statically bounded Solana account-data regions. Component
handles contain only compile-time descriptors; extraction erases them to checked account loads,
stores, and bounded control flow. `Sdk.Transient` reuses the official heap model and scratch plan
for invocation-local fixed vectors, byte writers, and composed codecs rather than introducing a
parallel allocator or lifetime. No native pointer or invocation-heap collection crosses the
contract boundary.

`Sdk.Memory` binds compile-time account-data spans to the official program-memory host functions.
It preserves `memcpy` non-overlap, `memmove` overlap, exact `memcmp` result bits, and `memset` byte
semantics while keeping every transient VM pointer behind the target-owned component boundary.

`Sdk.Pubkey` / `Sdk.Program` and the packed views in `Sdk.Token` provide allocation-free full-key,
canonical program-id, owner, and base-state validation. `Sdk.Pda`, `Sdk.System`, `Sdk.Token`,
`Sdk.AssociatedToken`, and `Sdk.Memo` provide compiler-erased names for current static program
effects. Applications no longer repeat key limbs, CPI tags, account metas, signer seeds, or
instruction-word recipes; the existing Runtime/IR verifier still owns their target validation.
-/
