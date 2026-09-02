import Examples.Svm.VersionedLedger
import Examples.Svm.VersionedMigrator
import ProofForge

/-!
Focused extraction and pure geometry/state checks for the fixed-account version codec. The two
examples remain direct imports so integration can add shared umbrellas and registries separately.
-/

namespace Tests.SvmVersionedCodecSpec

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Versioned

#pf_build Examples.Svm.VersionedLedger
#pf_build Examples.Svm.VersionedMigrator

#guard (Examples.Svm.VersionedLedger.fixed 1).wellFormed
#guard (Examples.Svm.VersionedLedger.fixed 2).wellFormed
#guard (Examples.Svm.VersionedMigrator.fixed 1).wellFormed
#guard (Examples.Svm.VersionedMigrator.fixed 2).wellFormed

#guard (Examples.Svm.VersionedLedger.fixed 1).header.discriminatorField == Field.scalar 1 1
#guard (Examples.Svm.VersionedLedger.fixed 1).header.versionField == Field.scalar 1 2
#guard (Examples.Svm.VersionedMigrator.fixed 1).migrateV1.fromVersion == 1
#guard (Examples.Svm.VersionedMigrator.fixed 1).header.supportedVersion == 2

-- Every logical account state is distinct.
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify 0 0 == Status.uninitialized
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify
    Examples.Svm.VersionedLedger.ledgerDiscriminator 1 == Status.ready
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify 7 1 == Status.wrongDiscriminator
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify
    Examples.Svm.VersionedLedger.ledgerDiscriminator 9 == Status.unsupportedVersion
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify 0 1 == Status.malformed
#guard (Examples.Svm.VersionedLedger.fixed 1).header.classify
    Examples.Svm.VersionedLedger.ledgerDiscriminator 0 == Status.malformed

-- Static malformed codecs and transition edges fail their compile-time gates.
#guard !({ (Examples.Svm.VersionedLedger.fixed 1).header with
  expectedDiscriminator := 0 }).wellFormed
#guard !({ (Examples.Svm.VersionedLedger.fixed 1).header with
  supportedVersion := 0 }).wellFormed
#guard !({ (Examples.Svm.VersionedLedger.fixed 1).header with
  versionField := Field.scalar 1 3 }).wellFormed
#guard !(Transition.from (Examples.Svm.VersionedMigrator.fixed 1).header 0).wellFormed
#guard !(Transition.from (Examples.Svm.VersionedMigrator.fixed 1).header 2).wellFormed

end Tests.SvmVersionedCodecSpec
