import ProofForge.Svm.AccountStorage

namespace ProofForge.Svm.BatchRecorder

/-- Solana rejects inner instructions whose serialized data and account-meta overhead exceed
1,280 bytes. One account meta consumes 34 bytes, leaving 1,246 bytes for recorder data. -/
def maxInnerDataBytes : Nat := 1246

/-- Recorder state is invocation-local scalar metadata. The variable-size byte buffer itself lives
in the official SVM bump heap; no heap address is exposed to source code or persistent storage. -/
def pointerStack : Nat := 416
def lengthStack : Nat := 424
def countStack : Nat := 432
def bumpStack : Nat := 440
def activeStack : Nat := 448
def stackScratchEnd : Nat := activeStack

/-- Fixed sink and capacity contract repeated by begin/append/finish calls. Account indexes are
external-relative, matching CPI metas and account-key words; physical state remains account zero. -/
structure Config where
  logAccount : Nat
  selfEntryTag : Nat
  authoritySeed : String
  maxBytes : Nat
  headerBytes : Nat
  countOffset : Nat
  maxRecords : Nat
  deriving BEq, Repr, Inhabited

private def byteString (value : String) : Bool :=
  value.toList.all (fun character => character.toNat ≤ 255)

def Config.wellFormed (config : Config) (accountLimit : Nat := 64) : Bool :=
  config.logAccount + 1 < accountLimit && config.selfEntryTag ≤ 255 &&
    !config.authoritySeed.isEmpty && config.authoritySeed.length ≤ 32 &&
    byteString config.authoritySeed && config.headerBytes > 0 &&
    config.countOffset + 2 ≤ config.headerBytes &&
    config.headerBytes ≤ config.maxBytes && config.maxBytes ≤ maxInnerDataBytes &&
    config.maxRecords > 0 && config.maxRecords ≤ 64

/-- Compile-time-shaped little-endian byte fragments. Dynamic content remains scalar values;
account keys are copied directly from the invocation's checked account headers. -/
inductive Word (V : Type) where
  | u8le (value : V)
  | u16le (value : V)
  | u32le (value : V)
  | u64le (value : V)
  | ascii (value : String)
  | programId
  | accountKey (account : Nat)
  deriving BEq, Repr, Inhabited

def Word.map (mapValue : α → β) : Word α → Word β
  | .u8le value => .u8le (mapValue value)
  | .u16le value => .u16le (mapValue value)
  | .u32le value => .u32le (mapValue value)
  | .u64le value => .u64le (mapValue value)
  | .ascii value => .ascii value
  | .programId => .programId
  | .accountKey account => .accountKey account

def Word.mapM [Monad m] (mapValue : α → m β) : Word α → m (Word β)
  | .u8le value => return .u8le (← mapValue value)
  | .u16le value => return .u16le (← mapValue value)
  | .u32le value => return .u32le (← mapValue value)
  | .u64le value => return .u64le (← mapValue value)
  | .ascii value => return .ascii value
  | .programId => return .programId
  | .accountKey account => return .accountKey account

def Word.values : Word V → Array V
  | .u8le value | .u16le value | .u32le value | .u64le value => #[value]
  | .ascii _ | .programId | .accountKey _ => #[]

def Word.byteSize : Word V → Nat
  | .u8le _ => 1
  | .u16le _ => 2
  | .u32le _ => 4
  | .u64le _ => 8
  | .ascii value => value.length
  | .programId | .accountKey _ => 32

def Word.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Word V → Bool
  | .u8le value | .u16le value | .u32le value | .u64le value => valueWellFormed value
  | .ascii value => !value.isEmpty && value.length ≤ maxInnerDataBytes && byteString value
  | .programId => true
  | .accountKey account => account + 1 < accountLimit

def Word.canonical (renderValue : V → String) : Word V → String
  | .u8le value => s!"b1:{renderValue value}"
  | .u16le value => s!"b2:{renderValue value}"
  | .u32le value => s!"b4:{renderValue value}"
  | .u64le value => s!"b8:{renderValue value}"
  | .ascii value => s!"a:{value.length}:{value}"
  | .programId => "p"
  | .accountKey account => s!"k:{account}"

private def wordsValues (words : Array (Word V)) : Array V :=
  words.flatMap Word.values

def wordsByteSize (words : Array (Word V)) : Nat :=
  words.foldl (init := 0) fun size word => size + word.byteSize

private def accountEffect (physicalAccount : Nat) : AccountStorage.EffectSummary :=
  { reads := #[physicalAccount] }

private def wordsEffects (words : Array (Word V)) : AccountStorage.EffectSummary :=
  words.foldl (init := {}) fun effects word =>
    match word with
    | .accountKey account => effects.merge (accountEffect (account + 1))
    | _ => effects

private def wordsCanonical (renderValue : V → String) (words : Array (Word V)) : String :=
  String.intercalate "," (words.map (Word.canonical renderValue)).toList

private def Config.canonical (config : Config) : String :=
  s!"{config.logAccount}.{config.selfEntryTag}.{config.authoritySeed}." ++
    s!"{config.maxBytes}.{config.headerBytes}.{config.countOffset}.{config.maxRecords}"

/-- Stateful bounded recorder protocol. `append` treats zero `enabled` as a no-op; otherwise it
flushes the current batch before an event that would exceed either static bound. `finish` always
flushes, including a header-only batch, and closes the invocation-local handle. -/
inductive Call (V : Type) where
  | begin (config : Config) (header : Array (Word V)) (bump : V)
  | append (config : Config) (enabled : V) (record : Array (Word V))
  | finish (config : Config)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .begin config header bump => .begin config (header.map (Word.map mapValue)) (mapValue bump)
  | .append config enabled record =>
      .append config (mapValue enabled) (record.map (Word.map mapValue))
  | .finish config => .finish config

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .begin config header bump =>
      return .begin config (← header.mapM (Word.mapM mapValue)) (← mapValue bump)
  | .append config enabled record =>
      return .append config (← mapValue enabled) (← record.mapM (Word.mapM mapValue))
  | .finish config => return .finish config

def Call.values : Call V → Array V
  | .begin _ header bump => wordsValues header |>.push bump
  | .append _ enabled record => #[enabled] ++ wordsValues record
  | .finish _ => #[]

def Call.effects : Call V → AccountStorage.EffectSummary
  | .begin config header _ => (accountEffect (config.logAccount + 1)).merge (wordsEffects header)
  | .append config _ record =>
      (accountEffect (config.logAccount + 1)).merge (wordsEffects record)
  | .finish config => accountEffect (config.logAccount + 1)

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  let fromAccounts := call.effects.reads.foldl (init := 0) fun current physicalAccount =>
    Nat.max current (physicalAccount + 1)
  call.values.foldl (init := fromAccounts) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .begin config header bump =>
      config.wellFormed accountLimit && 1 + wordsByteSize header == config.headerBytes &&
        header.all (Word.wellFormed valueWellFormed accountLimit) && valueWellFormed bump
  | .append config enabled record =>
      let recordBytes := wordsByteSize record
      config.wellFormed accountLimit && recordBytes > 0 &&
        config.headerBytes + recordBytes ≤ config.maxBytes &&
        valueWellFormed enabled && record.all (Word.wellFormed valueWellFormed accountLimit)
  | .finish config => config.wellFormed accountLimit

def Call.canonical (renderValue : V → String) : Call V → String
  | .begin config header bump =>
      s!"brb.{config.canonical}([{wordsCanonical renderValue header}],{renderValue bump})"
  | .append config enabled record =>
      s!"bra.{config.canonical}({renderValue enabled},[{wordsCanonical renderValue record}])"
  | .finish config => s!"brf.{config.canonical}"

def Call.usesCpi : Call V → Bool
  | _ => true

def Call.stackScratchEnd : Call V → Nat
  | _ => BatchRecorder.stackScratchEnd

def Call.rawSelfEntries : Call V → Array (Nat × String)
  | .begin config _ _ => #[(config.selfEntryTag, config.authoritySeed)]
  | .append .. | .finish .. => #[]

end ProofForge.Svm.BatchRecorder
