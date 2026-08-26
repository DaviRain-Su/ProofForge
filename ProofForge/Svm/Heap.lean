namespace ProofForge.Svm.Heap

/-- Fixed SVM virtual address at which Agave maps the program heap. -/
def startAddress : Nat := 0x300000000

/-- Solana's default program heap frame is 32 KiB. -/
def defaultFrameBytes : Nat := 32 * 1024

/-- The compute-budget program currently permits heap frames up to 256 KiB. -/
def maxFrameBytes : Nat := 256 * 1024

/-- Requested heap frames are expressed in whole KiB. -/
def frameGranularity : Nat := 1024

/-- The allocator stores its downward bump pointer in the first machine word. -/
def bumpWordBytes : Nat := 8

/-- `u128` has eight-byte alignment on sBPF, unlike most 64-bit hosts. -/
def alignOfU128 : Nat := 8

/-- A frame accepted by Solana's compute-budget limits. -/
def frameSizeValid (bytes : Nat) : Bool :=
  defaultFrameBytes ≤ bytes && bytes ≤ maxFrameBytes && bytes % frameGranularity == 0

/-- `Layout.align()` is nonzero and a power of two. -/
def alignmentValid (alignment : Nat) : Bool :=
  alignment != 0 && (alignment &&& (alignment - 1)) == 0

/-- Round an address down exactly as the Rust allocator's alignment mask does. -/
def alignDown (address alignment : Nat) : Nat :=
  if alignmentValid alignment then address - address % alignment else address

/--
State stored by the bounded SVM allocator. A zero bump is the untouched heap word; the first
allocation initializes it logically to the end of the selected frame before moving downward.
The frame size is an invocation/transaction choice and is never persistent account state.
-/
structure State where
  frameBytes : Nat
  bump : Nat := 0
  deriving BEq, Repr, Inhabited

def initial (frameBytes : Nat := defaultFrameBytes) : State :=
  { frameBytes }

def frameEnd (state : State) : Nat :=
  startAddress + state.frameBytes

def usableStart : Nat :=
  startAddress + bumpWordBytes

/-- Reject corrupted or out-of-frame allocator state instead of forming an SVM pointer. -/
def State.wellFormed (state : State) : Bool :=
  frameSizeValid state.frameBytes &&
    (state.bump == 0 || (usableStart ≤ state.bump && state.bump ≤ frameEnd state))

structure Allocation where
  pointer : Nat
  size : Nat
  alignment : Nat
  deriving BEq, Repr, Inhabited

/--
Model Solana's `BumpAllocator::alloc`: saturating subtraction, downward power-of-two alignment,
null/OOM when the candidate overlaps the reserved bump word, and no allocation outside the
selected bounded frame. The returned state is the value written to the heap's first word.
-/
def allocate (state : State) (size alignment : Nat) : Option (Allocation × State) :=
  if !state.wellFormed || !alignmentValid alignment then
    none
  else
    let position := if state.bump == 0 then frameEnd state else state.bump
    let candidate := alignDown (position - size) alignment
    if candidate < usableStart then
      none
    else
      some ({ pointer := candidate, size, alignment }, { state with bump := candidate })

/-- Solana's default bump allocator deliberately does not reclaim individual allocations. -/
def deallocate (state : State) (_allocation : Allocation) : State :=
  state

end ProofForge.Svm.Heap
