import ProofForge.Svm.Sdk.StorageModel
import ProofForge.Svm.Sdk.Versioned

/-!
# Versioned header 的 AccountWords 模型（sf-004）

把 `Header.classify` / `Header.initialize` / `Transition.apply` 在抽象账户字上解释，
与 SDK 控制流同构：同守卫、同写序（initialize：先 version 后 discriminator；
apply：只写 version）。宿主 `read`/`write` stub 不进入证明。
-/

namespace ProofForge.Svm.Sdk.VersionedModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage
open ProofForge.Svm.Sdk.StorageModel
open ProofForge.Svm.Sdk.Versioned

/-- 模型版读双字。 -/
def mVersionedRead (mem : AccountWords) (header : Header) : UInt64 × UInt64 :=
  (mReadField mem header.discriminatorField 0,
    mReadField mem header.versionField 0)

/-- 模型版 classify：委托纯函数。 -/
def mVersionedClassify (header : Header) (disc ver : UInt64) : UInt64 :=
  header.classify disc ver

/-- 模型版 initialize：与 `Header.initialize` 同守卫与写序。 -/
def mVersionedInitialize (mem : AccountWords) (header : Header) : AccountWords × UInt64 :=
  let status := header.classify (mReadField mem header.discriminatorField 0)
    (mReadField mem header.versionField 0)
  if status = Status.uninitialized then
    let mem := mWriteField mem header.versionField 0 header.supportedVersion
    let mem := mWriteField mem header.discriminatorField 0 header.expectedDiscriminator
    (mem, InitializeResult.initialized)
  else if status = Status.ready then (mem, InitializeResult.alreadyReady)
  else (mem, InitializeResult.rejected)

/-- 模型版 apply：与 `Transition.apply` 同守卫与写序。 -/
def mVersionedApply (mem : AccountWords) (transition : Transition) : AccountWords × UInt64 :=
  let header := transition.header
  if header.expectedDiscriminator = 0 || header.supportedVersion = 0 ||
      transition.fromVersion = 0 || transition.fromVersion = header.supportedVersion then
    (mem, TransitionResult.rejected)
  else
    let actualDiscriminator := mReadField mem header.discriminatorField 0
    let actualVersion := mReadField mem header.versionField 0
    if actualDiscriminator ≠ header.expectedDiscriminator then
      (mem, TransitionResult.rejected)
    else if actualVersion = header.supportedVersion then
      (mem, TransitionResult.alreadyCurrent)
    else if actualVersion = transition.fromVersion then
      (mWriteField mem header.versionField 0 header.supportedVersion,
        TransitionResult.transitioned)
    else (mem, TransitionResult.rejected)

/-! ## 几何桥 -/

theorem mFieldWord_versioned_disc (header : Header)
    (hwf : header.wellFormed = true) :
    mFieldWord header.discriminatorField 0 = some header.discriminatorField.firstWord := by
  have parts := Header.wellFormed_parts (header := header) (accountLimit := 64) hwf
  exact mFieldWord_scalar_header parts.1

theorem mFieldWord_versioned_ver (header : Header)
    (hwf : header.wellFormed = true) :
    mFieldWord header.versionField 0 = some header.versionField.firstWord := by
  have parts := Header.wellFormed_parts (header := header) (accountLimit := 64) hwf
  have hacc : header.versionField.region.account =
      header.discriminatorField.region.account :=
    scalarHeader_wf_account header.versionField header.discriminatorField.region.account parts.2.1
  have hsw : scalarHeaderWellFormed header.versionField
      header.versionField.region.account = true := by
    rw [hacc]; exact parts.2.1
  exact mFieldWord_scalar_header hsw

theorem versioned_disc_ne_ver (header : Header) (hwf : header.wellFormed = true) :
    header.discriminatorField.firstWord ≠ header.versionField.firstWord := by
  have parts := Header.wellFormed_parts (header := header) (accountLimit := 64) hwf
  have hadj : header.discriminatorField.firstWord + 1 = header.versionField.firstWord :=
    parts.2.2.1
  omega

/-- **全零 initialize**：返回 initialized，并写回 supportedVersion / expectedDiscriminator。 -/
theorem mVersionedInitialize_from_zero (mem : AccountWords) (header : Header)
    (hwf : header.wellFormed = true)
    (hd0 : mReadField mem header.discriminatorField 0 = 0)
    (hv0 : mReadField mem header.versionField 0 = 0) :
    (mVersionedInitialize mem header).2 = InitializeResult.initialized ∧
    mReadField (mVersionedInitialize mem header).1 header.versionField 0
      = header.supportedVersion ∧
    mReadField (mVersionedInitialize mem header).1 header.discriminatorField 0
      = header.expectedDiscriminator := by
  have parts := Header.wellFormed_parts (header := header) (accountLimit := 64) hwf
  have hclass : header.classify 0 0 = Status.uninitialized :=
    Header.classify_uninitialized header parts.2.2.2.1 parts.2.2.2.2
  have hwd := mFieldWord_versioned_disc header hwf
  have hwv := mFieldWord_versioned_ver header hwf
  have hne := versioned_disc_ne_ver header hwf
  -- Reduce definition under the zero/uninitialized hypotheses.
  have hproj :
      mVersionedInitialize mem header =
        (mWriteField (mWriteField mem header.versionField 0 header.supportedVersion)
          header.discriminatorField 0 header.expectedDiscriminator,
          InitializeResult.initialized) := by
    unfold mVersionedInitialize
    simp [hd0, hv0, hclass]
  rw [hproj]
  refine ⟨rfl, ?_, ?_⟩
  · -- version survives the later discriminator write
    have step :=
      mReadField_write_other
        (mWriteField mem header.versionField 0 header.supportedVersion)
        header.versionField header.discriminatorField 0 0 header.expectedDiscriminator
        hwv hwd hne.symm
    rw [step]
    exact mReadField_write_same mem header.versionField 0 header.supportedVersion _ hwv
  · exact mReadField_write_same
      (mWriteField mem header.versionField 0 header.supportedVersion)
      header.discriminatorField 0 header.expectedDiscriminator _ hwd

/-- **ready initialize**：alreadyReady，内存不变。 -/
theorem mVersionedInitialize_alreadyReady (mem : AccountWords) (header : Header)
    (hwf : header.wellFormed = true)
    (hd : mReadField mem header.discriminatorField 0 = header.expectedDiscriminator)
    (hv : mReadField mem header.versionField 0 = header.supportedVersion) :
    (mVersionedInitialize mem header).2 = InitializeResult.alreadyReady ∧
    (mVersionedInitialize mem header).1 = mem := by
  have parts := Header.wellFormed_parts (header := header) (accountLimit := 64) hwf
  have hclass : header.classify header.expectedDiscriminator header.supportedVersion
      = Status.ready :=
    Header.classify_ready header parts.2.2.2.1 parts.2.2.2.2
  have hproj : mVersionedInitialize mem header = (mem, InitializeResult.alreadyReady) := by
    unfold mVersionedInitialize
    simp [hd, hv, hclass, show Status.ready ≠ Status.uninitialized from by decide]
  rw [hproj]
  exact ⟨rfl, rfl⟩

/-- **reject initialize**：非 uninit/ready 时不写内存。 -/
theorem mVersionedInitialize_rejected_noop (mem : AccountWords) (header : Header)
    (hstatus :
      let s := header.classify (mReadField mem header.discriminatorField 0)
        (mReadField mem header.versionField 0)
      s ≠ Status.uninitialized ∧ s ≠ Status.ready) :
    (mVersionedInitialize mem header).2 = InitializeResult.rejected ∧
    (mVersionedInitialize mem header).1 = mem := by
  unfold mVersionedInitialize
  simp [hstatus.1, hstatus.2]

/-- **apply 成功**：fromVersion → supportedVersion；discriminator 不变。 -/
theorem mVersionedApply_transitioned (mem : AccountWords) (transition : Transition)
    (hwf : transition.wellFormed = true)
    (hd : mReadField mem transition.header.discriminatorField 0
      = transition.header.expectedDiscriminator)
    (hv : mReadField mem transition.header.versionField 0 = transition.fromVersion) :
    (mVersionedApply mem transition).2 = TransitionResult.transitioned ∧
    mReadField (mVersionedApply mem transition).1 transition.header.versionField 0
      = transition.header.supportedVersion ∧
    mReadField (mVersionedApply mem transition).1 transition.header.discriminatorField 0
      = transition.header.expectedDiscriminator := by
  have parts := Transition.wellFormed_parts (transition := transition) (accountLimit := 64) hwf
  have hparts := Header.wellFormed_parts (header := transition.header) (accountLimit := 64) parts.1
  have hwd := mFieldWord_versioned_disc transition.header parts.1
  have hwv := mFieldWord_versioned_ver transition.header parts.1
  have hne := versioned_disc_ne_ver transition.header parts.1
  have h0 : transition.header.expectedDiscriminator ≠ 0 := hparts.2.2.2.1
  have h1 : transition.header.supportedVersion ≠ 0 := hparts.2.2.2.2
  have h2 : transition.fromVersion ≠ 0 := parts.2.1
  have h3 : transition.fromVersion ≠ transition.header.supportedVersion := parts.2.2
  have hproj :
      mVersionedApply mem transition =
        (mWriteField mem transition.header.versionField 0 transition.header.supportedVersion,
          TransitionResult.transitioned) := by
    unfold mVersionedApply
    have hguard :
        ¬((transition.header.expectedDiscriminator = 0 ||
            transition.header.supportedVersion = 0 ||
            transition.fromVersion = 0 ||
            transition.fromVersion = transition.header.supportedVersion) = true) := by
      intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      -- Nested or: (((a ∨ b) ∨ c) ∨ d)
      rcases h with h | h
      · rcases h with h | h
        · rcases h with h | h
          · exact h0 h
          · exact h1 h
        · exact h2 h
      · exact h3 h
    rw [if_neg hguard, hd]
    have hdisc : ¬(transition.header.expectedDiscriminator ≠
        transition.header.expectedDiscriminator) := fun h => h rfl
    rw [if_neg hdisc, hv]
    have hcur : ¬(transition.fromVersion = transition.header.supportedVersion) := h3
    rw [if_neg hcur, if_pos rfl]
  rw [hproj]
  refine ⟨rfl, ?_, ?_⟩
  · exact mReadField_write_same mem transition.header.versionField 0
      transition.header.supportedVersion _ hwv
  · have step :=
      mReadField_write_other mem transition.header.discriminatorField
        transition.header.versionField 0 0 transition.header.supportedVersion
        hwd hwv hne
    simpa [hd] using step

end ProofForge.Svm.Sdk.VersionedModel
