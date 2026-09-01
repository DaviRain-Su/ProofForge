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

/-- CPI descriptors grow from `r10-2112` through the disjoint `[1088, 2112)` depth bank.
The scalar/CPI seam sits at 1088 (was 1024) so 9-account withdraw entries can hold a few more
join locals without overlapping invoke scratch. -/
def cpiBank : Bank :=
  { name := "cpi", baseStackOffset := 2112, capacityBytes := 1024, alignment := 8 }

/-- Expression, account-header, component, and scalar-local depths (`[0, 1088)`). -/
def scalarBank : Bank :=
  { name := "scalar", baseStackOffset := 1088, capacityBytes := 1088, alignment := 8 }

/-- Sysvar, PDA-seed, and bounded component depths (`[2112, 4096)`). -/
def deepBank : Bank :=
  { name := "deep", baseStackOffset := 4096, capacityBytes := 1984, alignment := 8 }

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

/-- One 16-byte Solana seed descriptor; a signer tail always appends one bump entry. -/
def seedEntryBytes : Nat := 16

/-- Stack distance of one region below the bank root (`r10 - distance`). -/
def Region.stackDistance (bank : Bank) (region : Region) : Nat :=
  bank.baseStackOffset - region.offset

/--
Typed regions of one bounded signer-seed tail: the copied static ASCII seed bytes, the
8-aligned bump byte, one 16-byte descriptor per declared seed plus the trailing bump entry,
and the single signer group. Non-copied seeds (state/account keys and fixed data slices) keep
size-zero copied bytes and reference their sources directly at emission time. Every offset and
capacity check is derived through `Plan.alloc`; the tail names no runtime pointer and no
account-persistent geometry.
-/
structure SignerSeedTail where
  scratch : Plan
  /-- Copied static ASCII seed bytes; empty when every seed is non-copied. -/
  bytes : Region
  /-- One bump byte, 8-aligned after the copied bytes. -/
  bump : Region
  /-- `seedCount` descriptors plus the trailing bump entry. -/
  entries : Region
  /-- The single fixed signer group descriptor. -/
  group : Region
  deriving BEq, Repr

namespace SignerSeedTail

/-- Entry-array span: one descriptor per declared seed plus the bump entry. -/
def entryBytes (seedCount : Nat) : Nat :=
  seedEntryBytes * (seedCount + 1)

/-- Offset of the trailing bump entry inside the entry array. -/
def bumpEntryOffset (tail : SignerSeedTail) : Nat :=
  tail.entries.endOffset - seedEntryBytes

end SignerSeedTail

/--
Append one typed signer-seed tail to `plan`. Capacity, alignment, and overlap are established
fail-closed by `Plan.alloc`; a tail that would leave the bank is rejected before emission.
-/
def Plan.signerSeedTail (plan : Plan) (copiedBytes seedCount : Nat) :
    Except String SignerSeedTail := do
  let bytes ← plan.alloc "seed" copiedBytes 1
  let bump ← bytes.plan.alloc "bump" 1 8
  let entries ← bump.plan.alloc "seedEntries" (SignerSeedTail.entryBytes seedCount) 8
  let group ← entries.plan.alloc "signerGroup" seedEntryBytes 8
  return {
    scratch := group.plan
    bytes := bytes.region
    bump := bump.region
    entries := entries.region
    group := group.region
  }

/-- Fixed 8-byte `sol_get_return_data` payload width, named once. -/
def returnDataPayloadBytes : Nat := 8

/-- Fixed 32-byte caller program-id staging width, named once. -/
def returnDataProgramIdBytes : Nat := 32

/--
Fixed bounded staging for one `sol_get_return_data` call: the 32-byte caller program id
followed by the fixed 8-byte payload. The window sits at the top of the shared deep sysvar
depth (`programId` rooted at `r10-3104`, `payload` at `r10-3072`); like the PDA-seed scratch it
shares that depth only because its contents are never live across another syscall.
-/
def returnDataBank : Bank :=
  { name := "returnData", baseStackOffset := 3104, capacityBytes := 40, alignment := 8 }

/-- Typed regions of one fixed return-data staging window. -/
structure ReturnDataStaging where
  scratch : Plan
  /-- 32-byte caller program id. -/
  programId : Region
  /-- Fixed 8-byte payload. -/
  payload : Region
  deriving BEq, Repr

/--
Open the fixed return-data staging window. Geometry is compile-time constant, so the only
failure mode is a malformed bank; the result stays invocation-local.
-/
def returnDataStaging : Except String ReturnDataStaging := do
  let plan ← Plan.open returnDataBank
  let programId ← plan.alloc "programId" returnDataProgramIdBytes returnDataBank.alignment
  let payload ← programId.plan.alloc "payload" returnDataPayloadBytes returnDataBank.alignment
  return {
    scratch := payload.plan
    programId := programId.region
    payload := payload.region
  }

end ProofForge.Svm.Scratch
