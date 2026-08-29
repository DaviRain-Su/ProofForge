import ProofForge.Attr
import ProofForge.Svm.Heap
import ProofForge.Svm.Scratch

/-!
# Invocation-local transient storage

Reusable SDK contracts for memory that dies with one SVM invocation. Persistent state belongs in
fixed-capacity account bytes; these descriptors instead model bounded heap buffers, fixed vectors,
byte writers, and composed scratch codecs.

The module builds on the existing target contracts rather than hiding them behind another
allocator: `Heap.State` remains the official downward bump state, `Scratch.Plan` remains the
aligned stack-bank planner, and `Scratch.Lifetime.invocationOnly` remains the sole lifetime.
Descriptors contain only compile-time geometry. A `HeapReservation` contains an allocator result
for the emitter/runtime boundary, but it is never an account-state handle.
-/

namespace ProofForge.Svm.Sdk.Transient

/-! ## Reusable multi-handle identity -/

/--
Compile-time handle slots for one transient container kind. Every bounded transient kind owns two
slots; each slot owns a private metadata bank (`Svm.Transient.Emit.slotCell`: four 8-byte cells,
`Svm.Transient.Emit.slotStride` bytes apart) and its own disjoint `begin` allocation from the
shared official downward bump heap. Simultaneous same-kind handles therefore never alias metadata
or payload, while `begin` on the same slot is the historical re-open that replaces that slot's
metadata only.

Handle identity never reaches top-level Ops, IR, the main emitter, or the runtime-leaf signature:
the single compiler-erased `capacity` word keeps the historical plain-payload encoding for slot 0
and packs the slot index above bit 32 for slot 1, so extraction still decodes one static literal
per operation and the target component splits the word back into capacity and slot.
-/
def maxHandleSlots : Nat := 2

/-- Bit weight of the slot field inside the compiler-erased handle word. -/
@[pf_inline] def handleSlotBit : Nat := 4294967296

/-- Payload capacity (or byte capacity) carried by the erased word's low 32 bits. -/
def handlePayload (word : Nat) : Nat := word % handleSlotBit

/-- Slot index carried by the erased word. -/
def handleSlot (word : Nat) : Nat := word / handleSlotBit

/-- Slot-0 handle word: the historical plain-payload encoding. -/
def firstSlotWord (payload : Nat) : Nat := payload

/-- Slot-1 handle word: the payload with its slot packed above bit 32. Additive on literals so
extraction decodes it without any new runtime leaf or opcode. -/
@[pf_inline] def secondSlotWord (payload : Nat) : Nat := payload + handleSlotBit

/-! ## Heap-backed buffers -/

/-- Compile-time geometry for one bounded invocation-local heap buffer. -/
structure HeapBuffer where
  name : String
  capacityBytes : Nat
  alignment : Nat := 8
  frameBytes : Nat := Heap.defaultFrameBytes
  deriving BEq, Repr, Inhabited

def HeapBuffer.wellFormed (buffer : HeapBuffer) : Bool :=
  !buffer.name.isEmpty && 0 < buffer.capacityBytes &&
    Heap.alignmentValid buffer.alignment &&
    Heap.frameSizeValid buffer.frameBytes &&
    Heap.bumpWordBytes + buffer.capacityBytes ≤ buffer.frameBytes

/-- Smallest legal compute-budget heap frame that can hold this buffer. -/
def HeapBuffer.minimumFrame (buffer : HeapBuffer) : Option Nat :=
  let needed := Heap.bumpWordBytes + buffer.capacityBytes
  let rounded :=
    Nat.max Heap.defaultFrameBytes
      ((needed + Heap.frameGranularity - 1) / Heap.frameGranularity * Heap.frameGranularity)
  if Heap.frameSizeValid rounded then some rounded else none

/-- A live allocator result and the heap state to thread into the next reservation. -/
structure HeapReservation where
  allocation : Heap.Allocation
  heap : Heap.State
  deriving BEq, Repr

/-- Reserve this buffer from an explicit invocation heap. -/
def HeapBuffer.reserve (buffer : HeapBuffer) (heap : Heap.State) :
    Except String HeapReservation :=
  if !buffer.wellFormed then
    .error s!"extract/unsupported: malformed {buffer.name} heap buffer descriptor"
  else if heap.frameBytes != buffer.frameBytes then
    .error s!"extract/unsupported: {buffer.name} heap buffer does not match the invocation frame"
  else
    match Heap.allocate heap buffer.capacityBytes buffer.alignment with
    | some (allocation, heap) => .ok { allocation, heap }
    | none => .error s!"extract/unsupported: {buffer.name} heap buffer is out of memory"

def HeapBuffer.reserveFresh (buffer : HeapBuffer) : Except String HeapReservation :=
  buffer.reserve (Heap.initial buffer.frameBytes)

/-! ## Fixed vectors and byte writers -/

/-- A fixed-capacity vector view over a heap buffer. The buffer owns exactly the vector payload;
length/capacity metadata belongs to the consumer's explicit codec. -/
structure FixedVec where
  buffer : HeapBuffer
  elementBytes : Nat
  capacity : Nat
  deriving BEq, Repr, Inhabited

def FixedVec.wellFormed (vector : FixedVec) : Bool :=
  vector.buffer.wellFormed && 0 < vector.elementBytes && 0 < vector.capacity &&
    vector.elementBytes * vector.capacity == vector.buffer.capacityBytes

def FixedVec.indexFits (vector : FixedVec) (index : Nat) : Bool :=
  vector.wellFormed && index < vector.capacity

/-- Fixed contract for a bounded serialized-record writer. The consumer owns the record codec;
this contract owns capacity, count-header geometry, and flush-before-overflow semantics. -/
structure ByteWriter where
  buffer : HeapBuffer
  headerBytes : Nat
  countOffset : Nat
  maxRecords : Nat
  deriving BEq, Repr, Inhabited

def ByteWriter.wellFormed (writer : ByteWriter) : Bool :=
  writer.buffer.wellFormed && 0 < writer.headerBytes &&
    writer.countOffset + 2 ≤ writer.headerBytes &&
    writer.headerBytes ≤ writer.buffer.capacityBytes && 0 < writer.maxRecords

def ByteWriter.recordFits (writer : ByteWriter)
    (lengthBytes count recordBytes : Nat) : Bool :=
  writer.wellFormed && recordBytes > 0 && count < writer.maxRecords &&
    writer.headerBytes ≤ lengthBytes &&
    lengthBytes + recordBytes ≤ writer.buffer.capacityBytes

def ByteWriter.flushRequired (writer : ByteWriter)
    (lengthBytes count recordBytes : Nat) : Bool :=
  !writer.recordFits lengthBytes count recordBytes

/-! ## Composed scratch codecs -/

/-- Scratch geometry needed to encode one signed CPI. This composes the reusable instruction and
signer-seed planners without introducing a second plan, bank, lifetime, or allocator contract. -/
structure SignedCpiCodec where
  instruction : Scratch.InstructionPlan
  signer : Scratch.SignerSeedTail
  deriving BEq, Repr

def SignedCpiCodec.plan (bank : Scratch.Bank) (buffer : Scratch.InstructionBuffer)
    (seedBytes seedCount : Nat) : Except String SignedCpiCodec := do
  let instruction ← Scratch.instructionPlan bank buffer
  let signer ← instruction.scratch.signerSeedTail seedBytes seedCount
  pure { instruction, signer }

end ProofForge.Svm.Sdk.Transient
