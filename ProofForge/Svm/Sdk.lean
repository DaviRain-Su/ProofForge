import ProofForge.Svm.Sdk.Account
import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.Queue
import ProofForge.Svm.Sdk.Pda
import ProofForge.Svm.Sdk.System
import ProofForge.Svm.Sdk.Token
import ProofForge.Svm.Sdk.Transient

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

`Sdk.Pda`, `Sdk.System`, and `Sdk.Token` provide compiler-erased names for the current static
PDA, fixed System Program, and fixed-account classic SPL Token effects. Applications no longer
repeat CPI tags, account metas, signer seeds, or instruction-word recipes; the existing
Runtime/IR verifier still owns their target validation.
-/
