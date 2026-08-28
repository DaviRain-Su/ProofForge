import ProofForge.Svm.Sdk.Account
import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.Queue

/-!
# ProofForge SVM SDK

Source-facing facade for reusable SVM components. Applications describe fixed account geometry
once, then compose persistent POD fields, bounded vectors, ordered maps, allocators, and FIFO
queues without defining protocol-specific operations or emitter cases.

All persistent state remains inside statically bounded Solana account-data regions. Component
handles contain only compile-time descriptors; extraction erases them to checked account loads,
stores, and bounded control flow. No native pointer or invocation-heap collection crosses the
contract boundary.
-/
