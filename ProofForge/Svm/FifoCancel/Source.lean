import ProofForge.Attr
import ProofForge.Svm.FifoCancel
import ProofForge.Svm.Runtime

namespace ProofForge.Svm.FifoCancel.Source

open ProofForge.Svm.Runtime

/-!
Source-facing operations for one statically configured FIFO cancellation component. The `Config`
is erased during extraction: only trader indexes and bounded cancel limits remain dynamic. This
layer introduces no runtime descriptor, heap container, pointer, operation, or emitter case.
-/

@[pf_inline] def begin : UInt64 := fifoCancelBegin

@[pf_inline] private def cancelSideWithCollateral (config : Config)
    (rootWord : Nat) (tree : AccountStorage.FifoRbTree)
    (baseLotsPerBaseUnitWord tickSizeWord : Nat) (traderIndex : UInt64) : UInt64 :=
  let region := tree.links.region
  let recorder := config.recorder
  fifoCancelSide (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
    (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
    (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
    (UInt64.ofNat config.owner.firstWord) (UInt64.ofNat config.size.firstWord)
    (UInt64.ofNat config.locked.firstWord) (UInt64.ofNat config.free.firstWord)
    (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
    (UInt64.ofNat config.locked.region.strideWords)
    (UInt64.ofNat config.locked.region.capacity) (if tree.bid then 1 else 0)
    (UInt64.ofNat baseLotsPerBaseUnitWord) (UInt64.ofNat tickSizeWord)
    (UInt64.ofNat recorder.logAccount) (UInt64.ofNat recorder.selfEntryTag)
    recorder.authoritySeed (UInt64.ofNat recorder.maxBytes) (UInt64.ofNat recorder.headerBytes)
    (UInt64.ofNat recorder.countOffset) (UInt64.ofNat recorder.maxRecords) traderIndex

/-- Cancel every order owned by `traderIndex` on one statically selected FIFO side. -/
@[pf_inline] def cancelSide (config : Config) (traderIndex : UInt64) : UInt64 :=
  match config.map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      match config.collateral with
      | .quote baseLotsPerBaseUnitWord tickSizeWord =>
          cancelSideWithCollateral config rootWord tree baseLotsPerBaseUnitWord tickSizeWord
            traderIndex
      | .base => cancelSideWithCollateral config rootWord tree 0 0 traderIndex

@[pf_inline] private def cancelUpToWithCollateral (config : Config)
    (rootWord : Nat) (tree : AccountStorage.FifoRbTree)
    (baseLotsPerBaseUnitWord tickSizeWord : Nat)
    (traderIndex tickLimit searchLimit cancelLimit : UInt64)
    (claimImmediately : Bool) : UInt64 :=
  let region := tree.links.region
  let recorder := config.recorder
  fifoCancelUpToSide (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
    (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
    (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
    (UInt64.ofNat config.owner.firstWord) (UInt64.ofNat config.size.firstWord)
    (UInt64.ofNat config.locked.firstWord) (UInt64.ofNat config.free.firstWord)
    (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
    (UInt64.ofNat config.locked.region.strideWords)
    (UInt64.ofNat config.locked.region.capacity) (if tree.bid then 1 else 0)
    (UInt64.ofNat baseLotsPerBaseUnitWord) (UInt64.ofNat tickSizeWord)
    (UInt64.ofNat recorder.logAccount) (UInt64.ofNat recorder.selfEntryTag)
    recorder.authoritySeed (UInt64.ofNat recorder.maxBytes) (UInt64.ofNat recorder.headerBytes)
    (UInt64.ofNat recorder.countOffset) (UInt64.ofNat recorder.maxRecords)
    traderIndex tickLimit searchLimit cancelLimit (if claimImmediately then 1 else 0)

/-- Cancel a bounded owned prefix on one static side. The claim policy is compile-time source
configuration; search and cancel limits remain invocation scalars. -/
@[pf_inline] def cancelUpTo (config : Config)
    (traderIndex tickLimit searchLimit cancelLimit : UInt64)
    (claimImmediately : Bool) : UInt64 :=
  match config.map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      match config.collateral with
      | .quote baseLotsPerBaseUnitWord tickSizeWord =>
          cancelUpToWithCollateral config rootWord tree baseLotsPerBaseUnitWord tickSizeWord
            traderIndex tickLimit searchLimit cancelLimit claimImmediately
      | .base =>
          cancelUpToWithCollateral config rootWord tree 0 0
            traderIndex tickLimit searchLimit cancelLimit claimImmediately

@[pf_inline] def quoteReleased : UInt64 := fifoCancelQuoteReleased
@[pf_inline] def baseReleased : UInt64 := fifoCancelBaseReleased
@[pf_inline] def eventCount : UInt64 := fifoCancelEventCount
@[pf_inline] def finish : UInt64 := fifoCancelFinish

end ProofForge.Svm.FifoCancel.Source
