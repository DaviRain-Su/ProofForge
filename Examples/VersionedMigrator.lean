import ProofForge.Attr
import ProofForge.Svm.Sdk.Versioned

/-!
An independent fixed-account consumer with an explicit migration policy. Fresh accounts start at
version 2; existing version-1 accounts move only through the separately exposed, one-edge
`migrateV1` entry. Initialization and ordinary payload access never migrate automatically.
-/

namespace Examples.VersionedMigrator

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.Versioned

def configDiscriminator : UInt64 := 0x434f4e4649473201
def currentVersion : UInt64 := 2
def legacyVersion : UInt64 := 1

/-- Storage account words 1/2 hold the version header; word 4 is this policy's payload. -/
structure Layout where
  header : Header
  migrateV1 : Transition
  value : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Layout.header Layout.migrateV1 Layout.value

@[pf_inline] def fixed (account : Nat) : Layout :=
  let header := Header.fixed account 1 configDiscriminator currentVersion
  { header
    migrateV1 := Transition.from header legacyVersion
    value := Field.scalar account 4 }

def Layout.wellFormed (layout : Layout) : Bool :=
  layout.header.wellFormed && layout.migrateV1.wellFormed &&
    layout.migrateV1.header == layout.header &&
    scalarHeaderWellFormed layout.value layout.header.discriminatorField.region.account &&
    layout.header.versionField.firstWord < layout.value.firstWord

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

/-- The sole allowed transition is the statically named edge `1 → 2`. -/
@[pf_entry] def migrateV1 (_s : State) : UInt64 :=
  (fixed 1).migrateV1.apply

@[pf_entry] def setCurrent (_s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if (fixed 1).header.isReady then
    let _ := write (fixed 1).value 0 value
    .ok ({ dummy := value }, value)
  else .error .incompatibleHeader

@[pf_entry] def current (_s : State) : UInt64 :=
  if (fixed 1).header.isReady then read (fixed 1).value 0 else 0

end Examples.VersionedMigrator
