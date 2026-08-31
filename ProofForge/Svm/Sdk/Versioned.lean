import ProofForge.Svm.Sdk.Storage

/-!
# Fixed-account version header

An allocation-free two-word codec for application-owned account data. A `Header` fixes the
runtime account, base word, exact nonzero discriminator, and one supported nonzero version in
compiler data. Operations erase to the existing typed `Field` reads and writes from
`Svm.Sdk.Storage`; this module adds no Runtime operation, pointer, collection, allocator, or
runtime-selected geometry.

The physical words are `(discriminator, version)`. Both zero means uninitialized. Exactly one
zero is malformed, while nonzero mismatches distinguish a foreign discriminator from an
unsupported version. Initialization only accepts the all-zero state, writes the version first,
and publishes the discriminator last. An already-ready header is an idempotent replay; every
other state is rejected without a write.

Version movement is deliberately separate. `Transition` describes exactly one compile-time edge
from a nonzero source version to the header's supported version. It never scans a range, chooses a
version at runtime, or silently migrates during inspection/initialization.
-/

namespace ProofForge.Svm.Sdk.Versioned

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage

/-- Two adjacent writable scalar words plus the exact logical identity they encode. -/
structure Header where
  discriminatorField : Field
  versionField : Field
  expectedDiscriminator : UInt64
  supportedVersion : UInt64
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Header.discriminatorField Header.versionField
  Header.expectedDiscriminator Header.supportedVersion

/-- Construct a fixed two-word header. `account` and `baseWord` are extraction-time geometry. -/
@[pf_inline] def Header.fixed (account baseWord : Nat)
    (discriminator version : UInt64) : Header :=
  { discriminatorField := Field.scalar account baseWord
    versionField := Field.scalar account (baseWord + 1)
    expectedDiscriminator := discriminator
    supportedVersion := version }

/-- Static codec contract: adjacent scalar words in one writable program-owned account, with a
nonzero discriminator and supported version. -/
def Header.wellFormed (header : Header) (accountLimit : Nat := 64) : Bool :=
  scalarHeaderWellFormed header.discriminatorField
      header.discriminatorField.region.account accountLimit &&
    scalarHeaderWellFormed header.versionField
      header.discriminatorField.region.account accountLimit &&
    header.discriminatorField.firstWord + 1 == header.versionField.firstWord &&
    header.expectedDiscriminator != 0 && header.supportedVersion != 0

namespace Status

/-- Both physical header words are zero. -/
def uninitialized : UInt64 := 0
/-- Both physical words exactly match this codec. -/
def ready : UInt64 := 1
/-- A nonzero physical discriminator belongs to another codec. -/
def wrongDiscriminator : UInt64 := 2
/-- The discriminator matches, but the nonzero version is not supported by this codec. -/
def unsupportedVersion : UInt64 := 3
/-- Exactly one physical header word is zero, or the static codec identity is invalid. -/
def malformed : UInt64 := 4

end Status

/-- Classify two already-read words. Zero/nonzero structural consistency is checked before exact
identity so mixed-zero state is always reported as malformed rather than foreign. -/
@[pf_inline] def Header.classify (header : Header)
    (actualDiscriminator actualVersion : UInt64) : UInt64 :=
  if header.expectedDiscriminator = 0 || header.supportedVersion = 0 then Status.malformed
  else if actualDiscriminator = 0 then
    if actualVersion = 0 then Status.uninitialized else Status.malformed
  else if actualVersion = 0 then Status.malformed
  else if actualDiscriminator ≠ header.expectedDiscriminator then Status.wrongDiscriminator
  else if actualVersion ≠ header.supportedVersion then Status.unsupportedVersion
  else Status.ready

/-- Read and classify the complete header. The second read is never skipped, so an undersized
account fails in the existing checked storage stub instead of being mistaken for a logical state. -/
@[pf_inline] def Header.inspect (header : Header) : UInt64 :=
  let actualDiscriminator := read header.discriminatorField 0
  let actualVersion := read header.versionField 0
  header.classify actualDiscriminator actualVersion

/-- Exact readiness predicate for application policy gates. -/
@[pf_inline] def Header.isReady (header : Header) : Bool :=
  header.inspect == Status.ready

namespace InitializeResult

/-- Initialization was rejected without mutation. -/
def rejected : UInt64 := 0
/-- The all-zero header was initialized. -/
def initialized : UInt64 := 1
/-- The exact header was already present; replay performed no write. -/
def alreadyReady : UInt64 := 2

end InitializeResult

/-- Initialize an all-zero header or accept an exact replay. Wrong, unsupported, and malformed
states return `rejected` without mutation. The discriminator is the final commit word. -/
@[pf_inline] def Header.initialize (header : Header) : UInt64 :=
  let status := header.inspect
  if status = Status.uninitialized then
    let _ := write header.versionField 0 header.supportedVersion
    let _ := write header.discriminatorField 0 header.expectedDiscriminator
    InitializeResult.initialized
  else if status = Status.ready then InitializeResult.alreadyReady
  else InitializeResult.rejected

/-- One explicit, statically bounded version edge. The target is the header's one supported
version; no intermediate or runtime-selected version is representable in this handle. -/
structure Transition where
  header : Header
  fromVersion : UInt64
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Transition.header Transition.fromVersion

/-- Name the sole source version accepted by this transition. -/
@[pf_inline] def Transition.from (header : Header) (version : UInt64) : Transition :=
  { header, fromVersion := version }

/-- Static transition contract: a valid header and one distinct nonzero source version. -/
def Transition.wellFormed (transition : Transition) (accountLimit : Nat := 64) : Bool :=
  transition.header.wellFormed accountLimit && transition.fromVersion != 0 &&
    transition.fromVersion != transition.header.supportedVersion

namespace TransitionResult

/-- The stored identity/version or the static edge did not match. No write occurred. -/
def rejected : UInt64 := 0
/-- The exact source version moved to the exact supported version. -/
def transitioned : UInt64 := 1
/-- The target version was already present; replay performed no write. -/
def alreadyCurrent : UInt64 := 2

end TransitionResult

/-- Apply exactly one explicit version edge. This operation never initializes a zero header,
repairs malformed state, accepts a foreign discriminator, or upgrades an unlisted source version. -/
@[pf_inline] def Transition.apply (transition : Transition) : UInt64 :=
  let header := transition.header
  if header.expectedDiscriminator = 0 || header.supportedVersion = 0 ||
      transition.fromVersion = 0 || transition.fromVersion = header.supportedVersion then
    TransitionResult.rejected
  else
    let actualDiscriminator := read header.discriminatorField 0
    let actualVersion := read header.versionField 0
    if actualDiscriminator ≠ header.expectedDiscriminator then TransitionResult.rejected
    else if actualVersion = header.supportedVersion then TransitionResult.alreadyCurrent
    else if actualVersion = transition.fromVersion then
      let _ := write header.versionField 0 header.supportedVersion
      TransitionResult.transitioned
    else TransitionResult.rejected

end ProofForge.Svm.Sdk.Versioned
