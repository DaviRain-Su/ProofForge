import ProofForge.Attr
import ProofForge.Svm.Sdk.Versioned

/-!
An independent fixed-account consumer with a strict fresh-or-current policy. It initializes
version 1 but never migrates foreign or old data. Payload access is available only after exact
header inspection succeeds.
-/

namespace Examples.VersionedLedger

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.Versioned

def ledgerDiscriminator : UInt64 := 0x4c45444745523101
def ledgerVersion : UInt64 := 1

/-- Storage account words 1/2 hold the version header; word 3 holds the application value. -/
structure Layout where
  header : Header
  value : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Layout.header Layout.value

@[pf_inline] def fixed (account : Nat) : Layout :=
  { header := Header.fixed account 1 ledgerDiscriminator ledgerVersion
    value := Field.scalar account 3 }

def Layout.wellFormed (layout : Layout) : Bool :=
  layout.header.wellFormed &&
    scalarHeaderWellFormed layout.value layout.header.discriminatorField.region.account &&
    layout.header.versionField.firstWord + 1 == layout.value.firstWord

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

/-- Strict initialization: exact replay is accepted, but no old version is upgraded. -/
@[pf_entry] def initializeStorage (_s : State) : UInt64 :=
  (fixed 1).header.initialize

/-- Publish one value only under the exact current header. -/
@[pf_entry] def record (_s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if (fixed 1).header.isReady then
    let _ := write (fixed 1).value 0 value
    .ok ({ dummy := value }, value)
  else .error .incompatibleHeader

/-- Incompatible storage never exposes payload bytes. -/
@[pf_entry] def current (_s : State) : UInt64 :=
  if (fixed 1).header.isReady then read (fixed 1).value 0 else 0

end Examples.VersionedLedger
