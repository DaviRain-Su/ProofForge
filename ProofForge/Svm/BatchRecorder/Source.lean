import ProofForge.Attr
import ProofForge.Svm.BatchRecorder
import ProofForge.Svm.Runtime

namespace ProofForge.Svm.BatchRecorder.Source

open ProofForge.Svm.Runtime

/-!
Source-facing operations for one statically configured bounded recorder. Extraction erases the
`Config`; only the header/record scalar values and PDA bump remain dynamic. The invocation-local
byte buffer stays inside the existing component and Solana bump allocator, and no pointer or
runtime-selected geometry is exposed to contract source.
-/

@[pf_inline] def begin (config : Config) (header : Array CpiWord) (bump : UInt64) : UInt64 :=
  batchRecorderBegin (UInt64.ofNat config.logAccount) (UInt64.ofNat config.selfEntryTag)
    config.authoritySeed (UInt64.ofNat config.maxBytes) (UInt64.ofNat config.headerBytes)
    (UInt64.ofNat config.countOffset) (UInt64.ofNat config.maxRecords) header bump

@[pf_inline] def append (config : Config) (enabled : UInt64) (record : Array CpiWord) : UInt64 :=
  batchRecorderAppend (UInt64.ofNat config.logAccount) (UInt64.ofNat config.selfEntryTag)
    config.authoritySeed (UInt64.ofNat config.maxBytes) (UInt64.ofNat config.headerBytes)
    (UInt64.ofNat config.countOffset) (UInt64.ofNat config.maxRecords) enabled record

@[pf_inline] def finish (config : Config) : UInt64 :=
  batchRecorderFinish (UInt64.ofNat config.logAccount) (UInt64.ofNat config.selfEntryTag)
    config.authoritySeed (UInt64.ofNat config.maxBytes) (UInt64.ofNat config.headerBytes)
    (UInt64.ofNat config.countOffset) (UInt64.ofNat config.maxRecords)

end ProofForge.Svm.BatchRecorder.Source
