import ProofForge.Attr
import ProofForge.Svm.Sdk.Versioned

/-!
Independent fixed-account consumer for `svm-sdk-006` payload migration. Fresh accounts start at
version 2 with the value in word 5. Legacy version-1 accounts store the value in word 4 and move
only through the explicit `migrateV1` edge, which copies word 4 → word 5 before publishing
version 2. Inspect/initialize never reshape payload.
-/

namespace Examples.Svm.VersionedPayloadMigrator

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.Versioned

def configDiscriminator : UInt64 := 0x5041594c4f414401
def currentVersion : UInt64 := 2
def legacyVersion : UInt64 := 1

/-- Words 1/2 = header; word 4 = legacy payload; word 5 = current payload after migration. -/
structure Layout where
  header : Header
  migrateV1 : PayloadTransition
  legacyValue : Field
  value : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Layout.header Layout.migrateV1 Layout.legacyValue Layout.value

@[pf_inline] def fixed (account : Nat) : Layout :=
  let header := Header.fixed account 1 configDiscriminator currentVersion
  let legacyValue := Field.scalar account 4
  let value := Field.scalar account 5
  { header
    migrateV1 := PayloadTransition.mkEdge header legacyVersion legacyValue value
    legacyValue
    value }

def Layout.wellFormed (layout : Layout) : Bool :=
  layout.header.wellFormed && layout.migrateV1.wellFormed &&
    layout.migrateV1.header == layout.header &&
    layout.migrateV1.source == layout.legacyValue &&
    layout.migrateV1.destination == layout.value &&
    scalarHeaderWellFormed layout.legacyValue layout.header.discriminatorField.region.account &&
    scalarHeaderWellFormed layout.value layout.header.discriminatorField.region.account &&
    layout.header.versionField.firstWord < layout.legacyValue.firstWord &&
    layout.legacyValue.firstWord < layout.value.firstWord

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | incompatibleHeader
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry] def inspectStorage (_s : State) : UInt64 :=
  (fixed 1).header.inspect

/-- Fresh-only version-2 initialization. A version-1 account is rejected, not auto-migrated. -/
@[pf_entry] def initializeStorage (_s : State) : UInt64 :=
  (fixed 1).header.initialize

/-- Sole allowed edge: copy legacy word 4 → word 5, then publish version 2. -/
@[pf_entry] def migrateV1 (_s : State) : UInt64 :=
  (fixed 1).migrateV1.apply

@[pf_entry] def setCurrent (_s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if (fixed 1).header.isReady then
    let _ := write (fixed 1).value 0 value
    .ok ({ dummy := value }, value)
  else .error .incompatibleHeader

@[pf_entry] def current (_s : State) : UInt64 :=
  if (fixed 1).header.isReady then read (fixed 1).value 0 else 0

end Examples.Svm.VersionedPayloadMigrator
