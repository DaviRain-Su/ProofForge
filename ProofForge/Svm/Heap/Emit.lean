import ProofForge.Core.IR
import ProofForge.Svm.Heap

/-!
# Shared SVM heap allocation emission

One implementation of the official Solana SDK downward bump allocator contract. Target-owned
components reserve bounded invocation memory through this helper instead of cloning allocator
assembly. The caller owns the result metadata and chooses its terminal OOM error; no pointer is
returned to source code or persistent state.
-/

namespace ProofForge.Svm.Heap.Emit

/-- Emit one aligned allocation from Solana's default 32 KiB SDK heap frame and store the pointer
in the caller-owned stack cell. Static malformed/OOM geometry fails compilation; invocation OOM
uses the caller's explicit terminal assembly. -/
def emitAllocate (kind label : String) (bytes alignment pointerStack : Nat)
    (oomFailure : String) : Except String String := do
  if kind.isEmpty || label.isEmpty || oomFailure.isEmpty then
    throw "assemble/svm: malformed heap allocation emitter identity"
  let initial := Heap.initial Heap.defaultFrameBytes
  let some _ := Heap.allocate initial bytes alignment
    | throw s!"assemble/svm: invalid default-heap allocation bytes={bytes} align={alignment}"
  let heapEnd := Heap.startAddress + Heap.defaultFrameBytes
  let usableStart := Heap.startAddress + Heap.bumpWordBytes
  let mask := Core.IR.u64Hex (~~~(UInt64.ofNat (alignment - 1)))
  return s!"\
  ; official Solana downward bump allocation bytes={bytes} align={alignment}
  lddw r4, {Heap.startAddress}
  ldxdw r2, [r4 + 0]
  jne r2, 0, {kind}_heap_position_{label}
  lddw r2, {heapEnd}
{kind}_heap_position_{label}:
  lddw r3, {bytes}
  jge r2, r3, {kind}_heap_subtract_{label}
{oomFailure}{kind}_heap_subtract_{label}:
  sub64 r2, r3
  lddw r3, 0x{mask}
  and64 r2, r3
  lddw r3, {usableStart}
  jge r2, r3, {kind}_heap_commit_{label}
{oomFailure}{kind}_heap_commit_{label}:
  stxdw [r4 + 0], r2
  stxdw [r10 - {pointerStack}], r2
"

end ProofForge.Svm.Heap.Emit
