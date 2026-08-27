import ProofForge.Svm.BatchRecorder

namespace ProofForge.Svm.FifoCancel

/-- Invocation-local cells shared by the bid and ask passes. They occupy the component deep-scratch
bank above CPI's 1,024..2,048 range. Complete tree validators finish before the side calls and may
therefore reuse the higher deep bank. Account headers and source scalar locals remain below 1,024.
Only scalar counters and keys survive a component call; no account or heap pointer does. -/
def eventIndexStack : Nat := 2056
def quoteReleasedStack : Nat := 2064
def baseReleasedStack : Nat := 2072
def hasCursorStack : Nat := 2080
def cursorPriceStack : Nat := 2088
def cursorSequenceStack : Nat := 2096
def traderIndexStack : Nat := 2104
def priceStack : Nat := 2112
def sequenceStack : Nat := 2120
def ownerStack : Nat := 2128
def sizeStack : Nat := 2136
def releasedStack : Nat := 2144
def lockedStack : Nat := 2152
def freeStack : Nat := 2160
def queryTempStack : Nat := 2168
def loopStack : Nat := 2176
def activeStack : Nat := 2184
def orderIndexStack : Nat := 2200
def tickLimitStack : Nat := 2264
def searchLimitStack : Nat := 2272
def cancelLimitStack : Nat := 2280
def scannedStack : Nat := 2288
def canceledStack : Nat := 2296
def queryScratchEnd : Nat := 2304

/-- Highest low-bank offset used transitively by the embedded recorder. Deep component scratch is
outside scalar-local planning and must not move account headers into the CPI bank. -/
def stackScratchEnd : Nat := BatchRecorder.stackScratchEnd

/-- Collateral unlocked by one whole-order cancellation. Bid orders release computed quote lots;
ask orders release their resting base lots directly. -/
inductive Collateral where
  | quote (baseLotsPerBaseUnitWord tickSizeWord : Nat)
  | base
  deriving BEq, Repr, Inhabited

/-- Static account-resident geometry for one ordered FIFO side. `map` owns the RB
topology and `(price, sequence)` key; the four fields select owner, resting size, and the trader's
locked/free balance pair. -/
structure Config where
  map : AccountStorage.RbMap
  owner : AccountStorage.Field
  size : AccountStorage.Field
  locked : AccountStorage.Field
  free : AccountStorage.Field
  collateral : Collateral
  recorder : BatchRecorder.Config
  deriving BEq, Repr, Inhabited

def Config.wellFormed (config : Config) (accountLimit : Nat := 64) : Bool :=
  config.map.wellFormed accountLimit && config.recorder.wellFormed accountLimit &&
    config.map.capacity ≤ 4096 &&
    match config.map with
    | .key4 .. => false
    | .fifo _ tree =>
        let mapRegion := tree.links.region
        let traderRegion := config.locked.region
        config.owner.wellFormed accountLimit && config.size.wellFormed accountLimit &&
          config.owner.widthWords == 1 && config.size.widthWords == 1 &&
          config.owner.region.sameShape mapRegion &&
          config.size.region.sameShape mapRegion &&
          config.locked.mutableOneBasedWord accountLimit &&
          config.free.mutableOneBasedWord accountLimit &&
          config.locked.region.sameShape config.free.region &&
          mapRegion.account == traderRegion.account &&
          (match config.collateral with
           | .base => !tree.bid
           | .quote baseLotsPerBaseUnitWord tickSizeWord =>
               tree.bid && baseLotsPerBaseUnitWord < AccountStorage.maxDataWord &&
                 tickSizeWord < AccountStorage.maxDataWord)

def Config.effects (config : Config) : AccountStorage.EffectSummary :=
  (AccountStorage.EffectSummary.forField config.owner).merge
    ((AccountStorage.EffectSummary.forField config.locked).merge
      { reads := #[config.recorder.logAccount + 1] })

/-- The accumulator is opened once, then one bid and one ask side can be canceled in order. The
side call expects complete tree/free-list validation to dominate it and removes only orders whose
stored owner equals the supplied one-based trader index. -/
inductive Call (V : Type) where
  | begin
  | cancelSide (config : Config) (traderIndex : V)
  | cancelUpTo (config : Config) (traderIndex tickLimit searchLimit cancelLimit : V)
      (claimImmediately : Bool)
  | finish
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .begin => .begin
  | .cancelSide config traderIndex => .cancelSide config (mapValue traderIndex)
  | .cancelUpTo config traderIndex tickLimit searchLimit cancelLimit claimImmediately =>
      .cancelUpTo config (mapValue traderIndex) (mapValue tickLimit) (mapValue searchLimit)
        (mapValue cancelLimit) claimImmediately
  | .finish => .finish

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .begin => return .begin
  | .cancelSide config traderIndex => return .cancelSide config (← mapValue traderIndex)
  | .cancelUpTo config traderIndex tickLimit searchLimit cancelLimit claimImmediately =>
      return .cancelUpTo config (← mapValue traderIndex) (← mapValue tickLimit)
        (← mapValue searchLimit) (← mapValue cancelLimit) claimImmediately
  | .finish => return .finish

def Call.values : Call V → Array V
  | .begin | .finish => #[]
  | .cancelSide _ traderIndex => #[traderIndex]
  | .cancelUpTo _ traderIndex tickLimit searchLimit cancelLimit _ =>
      #[traderIndex, tickLimit, searchLimit, cancelLimit]

def Call.effects : Call V → AccountStorage.EffectSummary
  | .begin | .finish => {}
  | .cancelSide config _ => config.effects
  | .cancelUpTo config .. => config.effects

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  let fromEffects := call.effects.reads.foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  call.values.foldl (init := fromEffects) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .begin | .finish => true
  | .cancelSide config traderIndex =>
      config.wellFormed accountLimit && valueWellFormed traderIndex
  | .cancelUpTo config traderIndex tickLimit searchLimit cancelLimit _ =>
      config.wellFormed accountLimit && valueWellFormed traderIndex &&
        valueWellFormed tickLimit && valueWellFormed searchLimit && valueWellFormed cancelLimit

def Call.canonical (renderValue : V → String) : Call V → String
  | .begin => "fcb"
  | .finish => "fcf"
  | .cancelSide config traderIndex =>
      match config.map with
      | .key4 .. => "invalid-fifo-cancel"
      | .fifo rootWord tree =>
          let region := tree.links.region
          let collateral := match config.collateral with
            | .base => "b"
            | .quote baseWord tickWord => s!"q{baseWord}.{tickWord}"
          s!"fcs.{region.account}.{rootWord}.{tree.links.firstWord}." ++
            s!"{tree.parentColor.firstWord}.{tree.price.firstWord}.{tree.sequence.firstWord}." ++
            s!"{config.owner.firstWord}.{config.size.firstWord}.{config.locked.firstWord}." ++
            s!"{config.free.firstWord}.{region.strideWords}.{region.capacity}.{collateral}." ++
            s!"{renderValue traderIndex}"
  | .cancelUpTo config traderIndex tickLimit searchLimit cancelLimit claimImmediately =>
      match config.map with
      | .key4 .. => "invalid-fifo-cancel-up-to"
      | .fifo rootWord tree =>
          let region := tree.links.region
          let collateral := match config.collateral with
            | .base => "b"
            | .quote baseWord tickWord => s!"q{baseWord}.{tickWord}"
          let claim := if claimImmediately then "c" else "f"
          s!"fcu.{region.account}.{rootWord}.{tree.links.firstWord}." ++
            s!"{tree.parentColor.firstWord}.{tree.price.firstWord}.{tree.sequence.firstWord}." ++
            s!"{config.owner.firstWord}.{config.size.firstWord}.{config.locked.firstWord}." ++
            s!"{config.free.firstWord}.{region.strideWords}.{region.capacity}.{collateral}.{claim}." ++
            s!"{renderValue traderIndex}.{renderValue tickLimit}." ++
            s!"{renderValue searchLimit}.{renderValue cancelLimit}"

def Call.usesCpi : Call V → Bool
  | .begin | .finish => false
  | .cancelSide .. | .cancelUpTo .. => true

def Call.stackScratchEnd : Call V → Nat
  | _ => FifoCancel.stackScratchEnd

def Call.rawSelfEntries : Call V → Array (Nat × String)
  | _ => #[]

/-- Read-only invocation-local outputs used by the outer protocol adapter after both side passes. -/
inductive Query where
  | eventCount
  | quoteReleased
  | baseReleased
  deriving BEq, Repr, Inhabited

def Query.stack : Query → Nat
  | .eventCount => eventIndexStack
  | .quoteReleased => quoteReleasedStack
  | .baseReleased => baseReleasedStack

def Query.canonical : Query → String
  | .eventCount => "fcqe"
  | .quoteReleased => "fcqq"
  | .baseReleased => "fcqb"

end ProofForge.Svm.FifoCancel
