import ProofForge.Svm.BatchRecorder

/-!
# BatchRecorder model (sf-013)

Pure L2 narration of the invocation-local recorder buffer. The byte list is the logical
`TransientModel.BytesWords` payload; allocator addresses, account words, CPI metadata, and the
stack cells used by the emitter are intentionally erased.

The model follows the SDK control flow:

* `mBegin` installs a rendered fixed-size header and opens the recorder.
* `mAppend` checks the active/config contract before the enabled flag.
* A full current batch is flushed before the record is appended to a fresh header.
* A record that cannot fit even in a fresh batch fails closed with `finishNeeded`.
* `mFinish` flushes unconditionally, including a count-zero header-only batch, then invalidates.
-/

namespace ProofForge.Svm.Sdk.BatchRecorderModel

/-- Account-independent projection of `BatchRecorder.Config` used by the pure byte model. -/
structure Geometry where
  maxBytes : Nat
  headerBytes : Nat
  countOffset : Nat
  maxRecords : Nat
  deriving Repr, DecidableEq, Inhabited

def Geometry.ofConfig (config : ProofForge.Svm.BatchRecorder.Config) : Geometry :=
  { maxBytes := config.maxBytes
    headerBytes := config.headerBytes
    countOffset := config.countOffset
    maxRecords := config.maxRecords }

/-- The same bounded writer geometry enforced by `Sdk.Transient.ByteWriter.wellFormed`. -/
def Geometry.WellFormed (geometry : Geometry) : Prop :=
  0 < geometry.headerBytes ∧
    geometry.countOffset + 2 ≤ geometry.headerBytes ∧
    geometry.headerBytes ≤ geometry.maxBytes ∧
    geometry.maxBytes ≤ ProofForge.Svm.BatchRecorder.maxInnerDataBytes ∧
    0 < geometry.maxRecords

instance (geometry : Geometry) : Decidable geometry.WellFormed := by
  unfold Geometry.WellFormed
  infer_instance

/--
Logical invocation-local recorder state. `count` is the abstract value overlaid at
`geometry.countOffset`; keeping it separate avoids introducing account-word storage into this
byte-level model.
-/
structure Recorder where
  geometry : Geometry
  active : Bool := false
  length : Nat := 0
  count : Nat := 0
  header : List UInt8 := []
  bytes : List UInt8 := []
  deriving Repr, DecidableEq, Inhabited

def Recorder.inactive (geometry : Geometry) : Recorder :=
  { geometry }

/-- Logical batch passed to the flush boundary. -/
structure Batch where
  bytes : List UInt8
  length : Nat
  count : Nat
  deriving Repr, DecidableEq, Inhabited

def Recorder.batch (recorder : Recorder) : Batch :=
  { bytes := recorder.bytes, length := recorder.length, count := recorder.count }

/-- Observable control result; only flush results carry a serialized batch. -/
inductive Outcome where
  | begun
  | skipped
  | appended
  | autoFlushed (batch : Batch)
  | finished (batch : Batch)
  | finishNeeded
  | stateError
  | geometryError
  deriving Repr, DecidableEq, Inhabited

def Outcome.emittedBytes : Outcome → Nat
  | .autoFlushed batch | .finished batch => batch.length
  | _ => 0

def activeFor (recorder : Recorder) (geometry : Geometry) : Prop :=
  recorder.active = true ∧ recorder.geometry = geometry

instance (recorder : Recorder) (geometry : Geometry) :
    Decidable (activeFor recorder geometry) := by
  unfold activeFor
  infer_instance

/-- A single record is statically admissible exactly when it fits after a fresh header. -/
def recordFitsFresh (geometry : Geometry) (record : List UInt8) : Prop :=
  record ≠ [] ∧ geometry.headerBytes + record.length ≤ geometry.maxBytes

instance (geometry : Geometry) (record : List UInt8) :
    Decidable (recordFitsFresh geometry record) := by
  unfold recordFitsFresh
  infer_instance

/-- The two dynamic preflight branches in `BatchRecorder.Emit.emitAppend`. -/
def appendNeedsFlush (recorder : Recorder) (record : List UInt8) : Prop :=
  recorder.geometry.maxRecords ≤ recorder.count ∨
    recorder.geometry.maxBytes < recorder.length + record.length

instance (recorder : Recorder) (record : List UInt8) :
    Decidable (appendNeedsFlush recorder record) := by
  unfold appendNeedsFlush
  infer_instance

/--
Open (or replace) the invocation-local recorder. `header` is the already-rendered full header,
including the leading entry tag. Invalid static geometry leaves the old state untouched.
-/
def mBegin (recorder : Recorder) (geometry : Geometry) (header : List UInt8) :
    Recorder × Outcome :=
  if geometry.WellFormed ∧ header.length = geometry.headerBytes then
    ({ geometry
       active := true
       length := geometry.headerBytes
       count := 0
       header
       bytes := header },
      .begun)
  else
    (recorder, .geometryError)

/--
Append one rendered record. A dynamic full condition flushes the current batch first, matching
the emitter. A statically oversized/empty record is rejected without a partial prefix.
-/
def mAppend (recorder : Recorder) (geometry : Geometry) (enabled : Bool)
    (record : List UInt8) : Recorder × Outcome :=
  if activeFor recorder geometry then
    if enabled then
      if recordFitsFresh geometry record then
        if appendNeedsFlush recorder record then
          ({ recorder with
               length := geometry.headerBytes + record.length
               count := 1
               bytes := recorder.header ++ record },
            .autoFlushed recorder.batch)
        else
          ({ recorder with
               length := recorder.length + record.length
               count := recorder.count + 1
               bytes := recorder.bytes ++ record },
            .appended)
      else
        (recorder, .finishNeeded)
    else
      (recorder, .skipped)
  else
    (recorder, .stateError)

/-- Flush even an empty batch, reset logical payload to the header, and invalidate the handle. -/
def mFinish (recorder : Recorder) (geometry : Geometry) : Recorder × Outcome :=
  if activeFor recorder geometry then
    ({ recorder with
         active := false
         length := geometry.headerBytes
         count := 0
         bytes := recorder.header },
      .finished recorder.batch)
  else
    (recorder, .stateError)

/-! ## Begin / append -/

/-- A valid begin followed by a fresh-fit append takes the direct append branch. -/
theorem mBegin_then_mAppend_ok
    (recorder : Recorder) (geometry : Geometry) (header record : List UInt8)
    (hgeometry : geometry.WellFormed)
    (hheader : header.length = geometry.headerBytes)
    (hrecord : record ≠ [])
    (hfits : geometry.headerBytes + record.length ≤ geometry.maxBytes) :
    mAppend (mBegin recorder geometry header).1 geometry true record =
      ({ geometry
         active := true
         length := geometry.headerBytes + record.length
         count := 1
         header
         bytes := header ++ record },
       .appended) := by
  have hcount : ¬geometry.maxRecords ≤ 0 := by
    have hpositive : 0 < geometry.maxRecords := hgeometry.2.2.2.2
    omega
  have hbytes :
      ¬geometry.maxBytes < geometry.headerBytes + record.length := by
    exact Nat.not_lt.mpr hfits
  simp [mBegin, hgeometry, hheader, mAppend, activeFor, recordFitsFresh,
    hrecord, hfits, appendNeedsFlush, hcount, hbytes]

/-! ## Full → flush and impossible-record rejection -/

theorem appendNeedsFlush_at_maxRecords
    (recorder : Recorder) (record : List UInt8)
    (hfull : recorder.geometry.maxRecords ≤ recorder.count) :
    appendNeedsFlush recorder record :=
  Or.inl hfull

theorem appendNeedsFlush_at_maxBytes
    (recorder : Recorder) (record : List UInt8)
    (hlength : recorder.length = recorder.geometry.maxBytes)
    (hrecord : record ≠ []) :
    appendNeedsFlush recorder record := by
  right
  cases record with
  | nil => exact (hrecord rfl).elim
  | cons _ tail =>
      simp only [List.length_cons]
      omega

/-- Reaching `maxRecords` flushes the old batch before installing the record in a fresh batch. -/
theorem mAppend_at_maxRecords_flushes
    (recorder : Recorder) (geometry : Geometry) (record : List UInt8)
    (hactive : activeFor recorder geometry)
    (hrecord : record ≠ [])
    (hfits : geometry.headerBytes + record.length ≤ geometry.maxBytes)
    (hfull : geometry.maxRecords ≤ recorder.count) :
    mAppend recorder geometry true record =
      ({ recorder with
           length := geometry.headerBytes + record.length
           count := 1
           bytes := recorder.header ++ record },
       .autoFlushed recorder.batch) := by
  have hflush : appendNeedsFlush recorder record := by
    left
    simpa [hactive.2] using hfull
  simp [mAppend, hactive, recordFitsFresh, hrecord, hfits, hflush]

/-- Filling all bytes makes every nonempty fresh-fit record take the flush-before-append branch. -/
theorem mAppend_at_maxBytes_flushes
    (recorder : Recorder) (geometry : Geometry) (record : List UInt8)
    (hactive : activeFor recorder geometry)
    (hlength : recorder.length = geometry.maxBytes)
    (hrecord : record ≠ [])
    (hfits : geometry.headerBytes + record.length ≤ geometry.maxBytes) :
    mAppend recorder geometry true record =
      ({ recorder with
           length := geometry.headerBytes + record.length
           count := 1
           bytes := recorder.header ++ record },
       .autoFlushed recorder.batch) := by
  have hflush : appendNeedsFlush recorder record := by
    apply appendNeedsFlush_at_maxBytes recorder record
    · simpa [hactive.2] using hlength
    · exact hrecord
  simp [mAppend, hactive, recordFitsFresh, hrecord, hfits, hflush]

/-- A record that cannot fit after an empty header requests finish/rejection and changes nothing. -/
theorem mAppend_finishNeeded_fail_closed
    (recorder : Recorder) (geometry : Geometry) (record : List UInt8)
    (hactive : activeFor recorder geometry)
    (hunfit : ¬recordFitsFresh geometry record) :
    mAppend recorder geometry true record = (recorder, .finishNeeded) := by
  simp [mAppend, hactive, hunfit]

/-! ## Inactive/stale fail-closed -/

theorem mAppend_stale
    (recorder : Recorder) (geometry : Geometry) (enabled : Bool) (record : List UInt8)
    (hstale : ¬activeFor recorder geometry) :
    mAppend recorder geometry enabled record = (recorder, .stateError) := by
  simp [mAppend, hstale]

theorem mAppend_inactive
    (recorder : Recorder) (geometry : Geometry) (enabled : Bool) (record : List UInt8)
    (hinactive : recorder.active = false) :
    mAppend recorder geometry enabled record = (recorder, .stateError) := by
  apply mAppend_stale
  simp [activeFor, hinactive]

theorem mAppend_stale_geometry
    (recorder : Recorder) (geometry : Geometry) (enabled : Bool) (record : List UInt8)
    (hstale : recorder.geometry ≠ geometry) :
    mAppend recorder geometry enabled record = (recorder, .stateError) := by
  apply mAppend_stale
  simp [activeFor, hstale]

theorem mFinish_stale
    (recorder : Recorder) (geometry : Geometry)
    (hstale : ¬activeFor recorder geometry) :
    mFinish recorder geometry = (recorder, .stateError) := by
  simp [mFinish, hstale]

theorem mFinish_inactive
    (recorder : Recorder) (geometry : Geometry)
    (hinactive : recorder.active = false) :
    mFinish recorder geometry = (recorder, .stateError) := by
  apply mFinish_stale
  simp [activeFor, hinactive]

theorem mFinish_stale_geometry
    (recorder : Recorder) (geometry : Geometry)
    (hstale : recorder.geometry ≠ geometry) :
    mFinish recorder geometry = (recorder, .stateError) := by
  apply mFinish_stale
  simp [activeFor, hstale]

/-! ## Empty finish is header-only -/

theorem mFinish_empty_after_begin
    (recorder : Recorder) (geometry : Geometry) (header : List UInt8)
    (hgeometry : geometry.WellFormed)
    (hheader : header.length = geometry.headerBytes) :
    mFinish (mBegin recorder geometry header).1 geometry =
      ({ geometry
         active := false
         length := geometry.headerBytes
         count := 0
         header
         bytes := header },
       .finished { bytes := header, length := geometry.headerBytes, count := 0 }) := by
  simp [mBegin, hgeometry, hheader, mFinish, activeFor, Recorder.batch]

/-- The unconditional empty flush accounts for exactly the configured fixed header bytes. -/
theorem mFinish_empty_emits_headerBytes
    (recorder : Recorder) (geometry : Geometry) (header : List UInt8)
    (hgeometry : geometry.WellFormed)
    (hheader : header.length = geometry.headerBytes) :
    Outcome.emittedBytes (mFinish (mBegin recorder geometry header).1 geometry).2 =
      geometry.headerBytes := by
  simp [mFinish_empty_after_begin recorder geometry header hgeometry hheader,
    Outcome.emittedBytes]

/-! ## State ownership -/

/--
All recorder fields are reconstructed from scalar geometry/lifecycle metadata and byte lists.
Consequently this account-independent model has no hidden account-word or heap-pointer field.
-/
theorem Recorder.no_account_words_or_heap_pointers (recorder : Recorder) :
    recorder =
      { geometry := recorder.geometry
        active := recorder.active
        length := recorder.length
        count := recorder.count
        header := recorder.header
        bytes := recorder.bytes } :=
  rfl

end ProofForge.Svm.Sdk.BatchRecorderModel
