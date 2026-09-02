import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.Versioned

/-!
# Versioned header model (sf-004)

L1 wf-parts + L2 AccountWords algebra for `Sdk.Versioned`.
-/

namespace ProofForge.Svm.Sdk.VersionedModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageModel
open ProofForge.Svm.Sdk.Versioned

/-! ## L1 wf parts -/

theorem header_wf_parts {header : Header} (hwf : header.wellFormed = true) :
    scalarHeaderWellFormed header.discriminatorField
        header.discriminatorField.region.account = true ∧
    scalarHeaderWellFormed header.versionField
        header.discriminatorField.region.account = true ∧
    header.discriminatorField.firstWord + 1 = header.versionField.firstWord ∧
    header.expectedDiscriminator ≠ 0 ∧
    header.supportedVersion ≠ 0 := by
  simp only [Header.wellFormed, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hwf
  exact ⟨hwf.1.1.1.1, hwf.1.1.1.2, hwf.1.1.2, hwf.1.2, hwf.2⟩

theorem transition_wf_parts {t : Transition} (hwf : t.wellFormed = true) :
    t.header.wellFormed = true ∧
    t.fromVersion ≠ 0 ∧
    t.fromVersion ≠ t.header.supportedVersion := by
  simp only [Transition.wellFormed, Bool.and_eq_true, bne_iff_ne] at hwf
  exact ⟨hwf.1.1, hwf.1.2, hwf.2⟩

theorem mFieldWord_header_disc {header : Header} (hwf : header.wellFormed = true) :
    mFieldWord header.discriminatorField 0 = some header.discriminatorField.firstWord :=
  mFieldWord_scalar_header (header_wf_parts hwf).1

theorem mFieldWord_header_ver {header : Header} (hwf : header.wellFormed = true) :
    mFieldWord header.versionField 0 = some header.versionField.firstWord := by
  have hv := (header_wf_parts hwf).2.1
  have hacc : header.versionField.region.account =
      header.discriminatorField.region.account := by
    simp only [scalarHeaderWellFormed, Bool.and_eq_true, beq_iff_eq] at hv
    -- nested ands: account = body is left.left.left.left.left.right
    exact hv.1.1.1.1.1.2
  have hsw : scalarHeaderWellFormed header.versionField
      header.versionField.region.account = true := by
    simpa [hacc.symm] using hv
  exact mFieldWord_scalar_header hsw

theorem header_disc_ne_ver {header : Header} (hwf : header.wellFormed = true) :
    header.discriminatorField.firstWord ≠ header.versionField.firstWord := by
  have := (header_wf_parts hwf).2.2.1
  omega

/-! ## Pure classify -/

theorem classify_uninitialized {header : Header}
    (hd : header.expectedDiscriminator ≠ 0) (hv : header.supportedVersion ≠ 0) :
    header.classify 0 0 = Status.uninitialized := by
  unfold Header.classify; simp [hd, hv]

theorem classify_ready {header : Header}
    (hd : header.expectedDiscriminator ≠ 0) (hv : header.supportedVersion ≠ 0) :
    header.classify header.expectedDiscriminator header.supportedVersion = Status.ready := by
  unfold Header.classify; simp [hd, hv]

theorem classify_wrongDisc {header : Header} {d v : UInt64}
    (hd : header.expectedDiscriminator ≠ 0) (hv : header.supportedVersion ≠ 0)
    (hd0 : d ≠ 0) (hv0 : v ≠ 0) (hne : d ≠ header.expectedDiscriminator) :
    header.classify d v = Status.wrongDiscriminator := by
  unfold Header.classify; simp [hd, hv, hd0, hv0, hne]

theorem classify_unsupported {header : Header} {v : UInt64}
    (hd : header.expectedDiscriminator ≠ 0) (hv : header.supportedVersion ≠ 0)
    (hv0 : v ≠ 0) (hne : v ≠ header.supportedVersion) :
    header.classify header.expectedDiscriminator v = Status.unsupportedVersion := by
  unfold Header.classify; simp [hd, hv, hv0, hne]

theorem classify_malformed_mixed {header : Header} {v : UInt64}
    (hd : header.expectedDiscriminator ≠ 0) (hv : header.supportedVersion ≠ 0)
    (hv0 : v ≠ 0) :
    header.classify 0 v = Status.malformed := by
  unfold Header.classify; simp [hd, hv, hv0]

/-! ## AccountWords model -/

def mVersionedInspect (mem : AccountWords) (header : Header) : UInt64 :=
  header.classify
    (mReadField mem header.discriminatorField 0)
    (mReadField mem header.versionField 0)

def mVersionedInitialize (mem : AccountWords) (header : Header) : AccountWords × UInt64 :=
  let status := mVersionedInspect mem header
  if status = Status.uninitialized then
    let mem := mWriteField mem header.versionField 0 header.supportedVersion
    let mem := mWriteField mem header.discriminatorField 0 header.expectedDiscriminator
    (mem, InitializeResult.initialized)
  else if status = Status.ready then (mem, InitializeResult.alreadyReady)
  else (mem, InitializeResult.rejected)

def mVersionedApply (mem : AccountWords) (t : Transition) : AccountWords × UInt64 :=
  let header := t.header
  if header.expectedDiscriminator = 0 ∨ header.supportedVersion = 0 ∨
      t.fromVersion = 0 ∨ t.fromVersion = header.supportedVersion then
    (mem, TransitionResult.rejected)
  else
    let actualD := mReadField mem header.discriminatorField 0
    let actualV := mReadField mem header.versionField 0
    if actualD ≠ header.expectedDiscriminator then (mem, TransitionResult.rejected)
    else if actualV = header.supportedVersion then (mem, TransitionResult.alreadyCurrent)
    else if actualV = t.fromVersion then
      (mWriteField mem header.versionField 0 header.supportedVersion,
        TransitionResult.transitioned)
    else (mem, TransitionResult.rejected)

/-! ## Initialize / apply theorems -/

theorem mVersionedInitialize_uninitialized (mem : AccountWords) (header : Header)
    (hwf : header.wellFormed = true)
    (hzD : mReadField mem header.discriminatorField 0 = 0)
    (hzV : mReadField mem header.versionField 0 = 0) :
    (mVersionedInitialize mem header).2 = InitializeResult.initialized ∧
    mVersionedInspect (mVersionedInitialize mem header).1 header = Status.ready := by
  have parts := header_wf_parts hwf
  have hwd := mFieldWord_header_disc hwf
  have hwv := mFieldWord_header_ver hwf
  have hne := header_disc_ne_ver hwf
  have hstatus : mVersionedInspect mem header = Status.uninitialized := by
    simp only [mVersionedInspect, hzD, hzV,
      classify_uninitialized parts.2.2.2.1 parts.2.2.2.2]
  have hpair :
      mVersionedInitialize mem header =
        (mWriteField (mWriteField mem header.versionField 0 header.supportedVersion)
          header.discriminatorField 0 header.expectedDiscriminator,
          InitializeResult.initialized) := by
    unfold mVersionedInitialize
    simp only [hstatus, ite_true]
  rw [hpair]
  refine ⟨rfl, ?_⟩
  simp only [mVersionedInspect]
  have hver : mReadField
      (mWriteField (mWriteField mem header.versionField 0 header.supportedVersion)
        header.discriminatorField 0 header.expectedDiscriminator)
      header.versionField 0 = header.supportedVersion := by
    have step := mReadField_write_other
      (mWriteField mem header.versionField 0 header.supportedVersion)
      header.versionField header.discriminatorField 0 0 header.expectedDiscriminator
      hwv hwd (Ne.symm hne)
    rw [step, mReadField_write_same _ _ _ _ _ hwv]
  have hdisc : mReadField
      (mWriteField (mWriteField mem header.versionField 0 header.supportedVersion)
        header.discriminatorField 0 header.expectedDiscriminator)
      header.discriminatorField 0 = header.expectedDiscriminator :=
    mReadField_write_same _ _ _ _ _ hwd
  rw [hdisc, hver, classify_ready parts.2.2.2.1 parts.2.2.2.2]

theorem mVersionedInitialize_alreadyReady (mem : AccountWords) (header : Header)
    (hwf : header.wellFormed = true)
    (hD : mReadField mem header.discriminatorField 0 = header.expectedDiscriminator)
    (hV : mReadField mem header.versionField 0 = header.supportedVersion) :
    mVersionedInitialize mem header = (mem, InitializeResult.alreadyReady) := by
  have parts := header_wf_parts hwf
  have hstatus : mVersionedInspect mem header = Status.ready := by
    simp only [mVersionedInspect, hD, hV,
      classify_ready parts.2.2.2.1 parts.2.2.2.2]
  have hne : Status.ready ≠ Status.uninitialized := by native_decide
  unfold mVersionedInitialize
  simp only [hstatus, if_neg hne, ↓reduceIte]

theorem mVersionedInitialize_wrongDisc (mem : AccountWords) (header : Header)
    (hwf : header.wellFormed = true) {d v : UInt64}
    (hD : mReadField mem header.discriminatorField 0 = d)
    (hV : mReadField mem header.versionField 0 = v)
    (hd0 : d ≠ 0) (hv0 : v ≠ 0) (hneD : d ≠ header.expectedDiscriminator) :
    mVersionedInitialize mem header = (mem, InitializeResult.rejected) := by
  have parts := header_wf_parts hwf
  have hstatus : mVersionedInspect mem header = Status.wrongDiscriminator := by
    simp only [mVersionedInspect, hD, hV,
      classify_wrongDisc parts.2.2.2.1 parts.2.2.2.2 hd0 hv0 hneD]
  have h1 : Status.wrongDiscriminator ≠ Status.uninitialized := by native_decide
  have h2 : Status.wrongDiscriminator ≠ Status.ready := by native_decide
  unfold mVersionedInitialize
  simp only [hstatus, if_neg h1, if_neg h2]

theorem mVersionedApply_transitioned (mem : AccountWords) (t : Transition)
    (hwf : t.wellFormed = true)
    (hD : mReadField mem t.header.discriminatorField 0 = t.header.expectedDiscriminator)
    (hV : mReadField mem t.header.versionField 0 = t.fromVersion) :
    (mVersionedApply mem t).2 = TransitionResult.transitioned ∧
    mReadField (mVersionedApply mem t).1 t.header.versionField 0 =
      t.header.supportedVersion ∧
    mReadField (mVersionedApply mem t).1 t.header.discriminatorField 0 =
      t.header.expectedDiscriminator := by
  have tp := transition_wf_parts hwf
  have parts := header_wf_parts tp.1
  have hwv := mFieldWord_header_ver tp.1
  have hwd := mFieldWord_header_disc tp.1
  have hneWords := header_disc_ne_ver tp.1
  have hguard : ¬ (t.header.expectedDiscriminator = 0 ∨ t.header.supportedVersion = 0 ∨
      t.fromVersion = 0 ∨ t.fromVersion = t.header.supportedVersion) := by
    intro h; rcases h with h | h | h | h
    · exact parts.2.2.2.1 h
    · exact parts.2.2.2.2 h
    · exact tp.2.1 h
    · exact tp.2.2 h
  have happly :
      mVersionedApply mem t =
        (mWriteField mem t.header.versionField 0 t.header.supportedVersion,
          TransitionResult.transitioned) := by
    unfold mVersionedApply
    rw [if_neg hguard]
    -- disc mismatch branch
    have hneDisc : ¬ (mReadField mem t.header.discriminatorField 0 ≠
        t.header.expectedDiscriminator) := by simp [hD]
    rw [if_neg hneDisc]
    -- already-current branch
    have hneCur : ¬ (mReadField mem t.header.versionField 0 =
        t.header.supportedVersion) := by
      rw [hV]; exact tp.2.2
    rw [if_neg hneCur]
    -- fromVersion match
    have hfrom : mReadField mem t.header.versionField 0 = t.fromVersion := hV
    simp only [hfrom, ite_true]
  rw [happly]
  refine ⟨rfl, mReadField_write_same _ _ _ _ _ hwv, ?_⟩
  have hkeep := mReadField_write_other mem t.header.discriminatorField t.header.versionField
      0 0 t.header.supportedVersion hwd hwv hneWords
  exact hkeep.trans hD

theorem mVersionedApply_alreadyCurrent (mem : AccountWords) (t : Transition)
    (hwf : t.wellFormed = true)
    (hD : mReadField mem t.header.discriminatorField 0 = t.header.expectedDiscriminator)
    (hV : mReadField mem t.header.versionField 0 = t.header.supportedVersion) :
    mVersionedApply mem t = (mem, TransitionResult.alreadyCurrent) := by
  have tp := transition_wf_parts hwf
  have parts := header_wf_parts tp.1
  have hguard : ¬ (t.header.expectedDiscriminator = 0 ∨ t.header.supportedVersion = 0 ∨
      t.fromVersion = 0 ∨ t.fromVersion = t.header.supportedVersion) := by
    intro h; rcases h with h | h | h | h
    · exact parts.2.2.2.1 h
    · exact parts.2.2.2.2 h
    · exact tp.2.1 h
    · exact tp.2.2 h
  unfold mVersionedApply
  rw [if_neg hguard]
  have hneDisc : ¬ (mReadField mem t.header.discriminatorField 0 ≠
      t.header.expectedDiscriminator) := by simp [hD]
  rw [if_neg hneDisc]
  simp only [hV, ite_true]

end ProofForge.Svm.Sdk.VersionedModel

