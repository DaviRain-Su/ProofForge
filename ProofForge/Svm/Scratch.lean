import ProofForge.Svm.Heap

/-!
# Bounded SVM scratch planning

This target-local plan layer owns invocation scratch geometry. It allocates aligned regions in a
fixed stack bank and rejects malformed banks, duplicate names, invalid alignment, and OOM before
emission. Plans contain only compile-time byte counts; they cannot carry a runtime pointer or be
persisted into account state.
-/

namespace ProofForge.Svm.Scratch

inductive Lifetime where
  | invocationOnly
  deriving BEq, Repr, Inhabited

/-- One compile-time region above a bank root. No address or account offset is representable. -/
structure Region where
  name : String
  offset : Nat
  size : Nat
  deriving BEq, Repr, Inhabited

def Region.endOffset (region : Region) : Nat :=
  region.offset + region.size

def Region.disjointFrom (a b : Region) : Bool :=
  a.endOffset ≤ b.offset || b.endOffset ≤ a.offset

/-- A fixed stack interval rooted `baseStackOffset` bytes below sBPF register `r10`. -/
structure Bank where
  name : String
  baseStackOffset : Nat
  capacityBytes : Nat
  alignment : Nat
  lifetime : Lifetime := .invocationOnly
  deriving BEq, Repr, Inhabited

def Bank.lowWater (bank : Bank) : Nat :=
  bank.baseStackOffset - bank.capacityBytes

def Bank.wellFormed (bank : Bank) : Bool :=
  !bank.name.isEmpty && Heap.alignmentValid bank.alignment &&
    0 < bank.capacityBytes && bank.capacityBytes ≤ bank.baseStackOffset

def Bank.disjoint (a b : Bank) : Bool :=
  a.baseStackOffset ≤ b.lowWater || b.baseStackOffset ≤ a.lowWater

/-- CPI descriptors grow from `r10-2048` through the disjoint `[1024, 2048)` depth bank. -/
def cpiBank : Bank :=
  { name := "cpi", baseStackOffset := 2048, capacityBytes := 1024, alignment := 8 }

/-- Existing expression, account-header, component, and scalar-local depths. -/
def scalarBank : Bank :=
  { name := "scalar", baseStackOffset := 1024, capacityBytes := 1024, alignment := 8 }

/-- Existing sysvar, PDA-seed, and bounded component depths. -/
def deepBank : Bank :=
  { name := "deep", baseStackOffset := 4096, capacityBytes := 2048, alignment := 8 }

structure Plan where
  bank : Bank
  regions : Array Region
  cursor : Nat
  deriving BEq, Repr

structure Allocation where
  plan : Plan
  region : Region
  deriving BEq, Repr

/-- Open only a valid invocation-local stack bank. -/
def Plan.open (bank : Bank) : Except String Plan :=
  if bank.wellFormed then
    .ok { bank, regions := #[], cursor := 0 }
  else
    .error s!"extract/unsupported: malformed {bank.name} scratch bank"

def Plan.frameBytes (plan : Plan) : Nat :=
  plan.cursor

def Plan.region? (plan : Plan) (name : String) : Option Region :=
  plan.regions.find? (·.name == name)

/--
Allocate one region and return its typed result with the extended plan. Returning the region
directly keeps emitters from looking up layout offsets through partial string APIs.
-/
def Plan.alloc (plan : Plan) (name : String) (size alignment : Nat) : Except String Allocation :=
  if name.isEmpty then
    .error s!"extract/unsupported: {plan.bank.name} scratch region has an empty name"
  else if (plan.region? name).isSome then
    .error s!"extract/unsupported: {plan.bank.name} scratch region '{name}' is duplicated"
  else if !Heap.alignmentValid alignment then
    .error s!"extract/unsupported: {plan.bank.name} scratch '{name}' has invalid alignment {alignment}"
  else
    let offset := Heap.alignUp plan.cursor alignment
    let region : Region := { name, offset, size }
    if region.endOffset ≤ plan.bank.capacityBytes then
      .ok {
        region
        plan := { plan with regions := plan.regions.push region, cursor := region.endOffset }
      }
    else
      .error (s!"extract/unsupported: {plan.bank.name} scratch '{name}' requires " ++
        s!"{region.endOffset} bytes, maximum is {plan.bank.capacityBytes}")

/-- Regions returned by `alloc` are ordered and therefore pairwise non-overlapping. -/
def laidOutFrom (high : Nat) : List Region → Bool
  | [] => true
  | region :: rest => high ≤ region.offset && laidOutFrom region.endOffset rest

def Plan.laidOut (plan : Plan) : Bool :=
  plan.cursor ≤ plan.bank.capacityBytes && laidOutFrom 0 plan.regions.toList

/-- Static inputs for one Solana C instruction descriptor and its account arrays. -/
structure InstructionBuffer where
  metaCount : Nat
  dataBytes : Nat
  accountCount : Nat
  deriving BEq, Repr, Inhabited

namespace InstructionBuffer

/-- Loader ABI sizes, named once instead of repeated as emitter offsets. -/
def accountMetaBytes : Nat := 16
def instructionDescriptorBytes : Nat := 40
def accountInfoBytes : Nat := 56
def dataAlignment : Nat := 8

def metaBytes (buffer : InstructionBuffer) : Nat :=
  accountMetaBytes * buffer.metaCount

def instructionOffset (buffer : InstructionBuffer) : Nat :=
  buffer.metaBytes

def dataOffset (buffer : InstructionBuffer) : Nat :=
  buffer.instructionOffset + instructionDescriptorBytes

def dataSpan (buffer : InstructionBuffer) : Nat :=
  Heap.alignUp buffer.dataBytes dataAlignment

def infoOffset (buffer : InstructionBuffer) : Nat :=
  buffer.dataOffset + buffer.dataSpan

def infoBytes (buffer : InstructionBuffer) : Nat :=
  accountInfoBytes * buffer.accountCount

def seedOffset (buffer : InstructionBuffer) : Nat :=
  buffer.infoOffset + buffer.infoBytes

end InstructionBuffer

/-- Typed regions of the fixed instruction-buffer prefix. Callers extend `scratch` with seeds,
return-data staging, or other bounded invocation-only tails. -/
structure InstructionPlan where
  scratch : Plan
  metas : Region
  instruction : Region
  data : Region
  infos : Region
  deriving BEq, Repr

def instructionPlan (bank : Bank) (buffer : InstructionBuffer) : Except String InstructionPlan := do
  let plan ← Plan.open bank
  let metas ← plan.alloc "metas" buffer.metaBytes bank.alignment
  let instruction ← metas.plan.alloc "instruction"
    InstructionBuffer.instructionDescriptorBytes bank.alignment
  let data ← instruction.plan.alloc "data" buffer.dataSpan bank.alignment
  let infos ← data.plan.alloc "infos" buffer.infoBytes bank.alignment
  return {
    scratch := infos.plan
    metas := metas.region
    instruction := instruction.region
    data := data.region
    infos := infos.region
  }

end ProofForge.Svm.Scratch
