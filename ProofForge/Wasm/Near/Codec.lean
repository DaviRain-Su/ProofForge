import ProofForge.Core.Codec

/-!
# NEAR boundary codec plans

Target-owned canonical Borsh geometry for the first bounded byte/string entry slice. The source
carrier is a fixed scalar frame (`UInt32` length plus `capacity` UInt8 slots); NEAR wire input is
the canonical `u32_le length || active bytes` prefix. No source Vector or target pointer survives.
-/

namespace ProofForge.Wasm.Near.Codec

/-- Bound generated scalar locals and linear-memory work while retaining useful AccountId-sized
payloads. This is a ProofForge compilation limit, not a Borsh or nearcore protocol limit. -/
def maxBoundedBytesCapacity : Nat := 64

/-- Storage values and copied register results reuse the public bounded-byte compiler budget.
This is not nearcore's protocol limit. A capacity of at least one still represents an empty byte
sequence through runtime `length = 0`; internal raw keys have their separate bound below. -/
def storageCapacityValid (capacity : Nat) : Bool :=
  1 ≤ capacity && capacity ≤ maxBoundedBytesCapacity

/-- Internal raw-storage keys may additionally hold `Prefix4 || Borsh(AccountId)`, whose largest
injective representation is four namespace bytes, a four-byte length, and 64 active UTF-8 bytes.
Values, register results, public bounded ABI frames, logs, and promises retain the 64-byte budget. -/
def maxRawStorageKeyCapacity : Nat := 72

def rawStorageKeyCapacityValid (capacity : Nat) : Bool :=
  1 ≤ capacity && capacity ≤ maxRawStorageKeyCapacity

/-- Keep the specialized event's statically selected scalar frame below nearcore's per-function
control-flow limit. This is a ProofForge compilation limit, not a NEP-141 memo limit. -/
def maxNep141MemoCapacity : Nat := 16

/-- A single worst-case memo event must fit nearcore's 16,384-byte cumulative log budget even
when it is the first log. Transfer has the largest fixed envelope (938 bytes); the memo field prefix
adds ten bytes and each active source byte can expand to six JSON bytes. -/
def nep141MemoCapacityValid (capacity : Nat) : Bool :=
  storageCapacityValid capacity && capacity ≤ maxNep141MemoCapacity &&
    938 + 10 + capacity * 6 ≤ 16384

private def accountIdSeparator (byte : UInt8) : Bool :=
  byte == 0x2d || byte == 0x2e || byte == 0x5f

private def accountIdByte (byte : UInt8) : Bool :=
  (0x61 ≤ byte && byte ≤ 0x7a) || (0x30 ≤ byte && byte ≤ 0x39) ||
    accountIdSeparator byte

/-- Exact static NEAR AccountId syntax used for compile-time promise receivers: 2..64 ASCII
bytes, lowercase letters/digits plus `-`, `.`, `_`, with no leading, trailing, or adjacent
separators. This mirrors nearcore's account-id parser and adds no `.near`/`.test` policy. -/
def accountIdLiteralValid (accountId : String) : Bool :=
  let bytes := accountId.toUTF8.data
  if bytes.size < 2 || 64 < bytes.size then false
  else
    let state := bytes.foldl (init := (true, true)) fun (valid, previousSeparator) byte =>
      let separator := accountIdSeparator byte
      (valid && accountIdByte byte && !(separator && previousSeparator), separator)
    state.1 && !state.2

/-- Static near-sdk `String` method-name bound. The host consumes raw bytes; ProofForge keeps the
SDK-facing UTF-8 literal nonempty and within nearcore's 256-byte action limit. -/
def promiseMethodLiteralValid (method : String) : Bool :=
  let size := method.toUTF8.size
  1 ≤ size && size ≤ 256

structure BorshInputPlan where
  capacity : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

def BorshInputPlan.localCount (plan : BorshInputPlan) : Nat := 1 + plan.capacity

def BorshInputPlan.canonical (plan : BorshInputPlan) : String :=
  s!"near-borsh-{if plan.validateUtf8 then "string" else "bytes"}-v1(capacity={plan.capacity})"

def inputPlan : Core.Codec.Schema → Except String BorshInputPlan
  | .boundedBytes capacity => do
      unless storageCapacityValid capacity do
        throw s!"near/codec: bounded bytes capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := false }
  | .boundedString capacity => do
      unless storageCapacityValid capacity do
        throw s!"near/codec: bounded string capacity must be in 1..{maxBoundedBytesCapacity}"
      pure { capacity, validateUtf8 := true }
  | _ => throw "near/codec: input plan requires bounded bytes or string"

def BorshInputPlan.valueIndex? (plan : BorshInputPlan) (name : String) : Option Nat := do
  unless name.startsWith "values_" do none
  let index ← (name.drop 7).toNat?
  if index < plan.capacity then some index else none

/-- The bounded AccountId object subset allows at most 32 JSON whitespace bytes across the whole
document. This is a ProofForge resource bound, not a serde_json or nearcore limit. -/
def maxJsonAccountWhitespace : Nat := 32

/-- Exact maximum wire geometry: `{"account_id":""}` (17 bytes), 64 bytes each escaped as six
ASCII bytes, and the separately bounded whitespace allowance. -/
def maxJsonAccountInputBytes : Nat := 17 + 64 * 6 + maxJsonAccountWhitespace

/-- Canonical quoted-u128 input allows the same bounded structural whitespace and up to 39
decoded decimal digits, each represented raw or as one six-byte `\u00xx` escape. -/
def maxJsonU128Whitespace : Nat := 32
def maxJsonU128InputBytes : Nat := 13 + 39 * 6 + maxJsonU128Whitespace

/-- Optional memo input has 11 structural bytes in its largest string form, at most sixteen
decoded UTF-8 bytes each represented by a six-byte JSON escape, and separately bounded whitespace. -/
def maxJsonMemoWhitespace : Nat := 32
def maxJsonMemoInputBytes : Nat := 11 + 16 * 6 + maxJsonMemoWhitespace

/-- Required message string: `{"msg":""}` is ten structural bytes. -/
def maxJsonMessageWhitespace : Nat := 32
def maxJsonMessageInputBytes : Nat := 10 + 64 * 6 + maxJsonMessageWhitespace

/-- Exact largest combined transfer-shaped wire: 40 structural bytes for three string fields,
64 AccountId bytes, 39 decimal digits, and 16 memo bytes each in six-byte JSON escapes, plus the
single aggregate structural-whitespace allowance. -/
def maxJsonFtTransferWhitespace : Nat := 32
def maxJsonFtTransferInputBytes : Nat :=
  40 + 64 * 6 + 39 * 6 + 16 * 6 + maxJsonFtTransferWhitespace

/-- Exact largest transfer-call-shaped wire: 49 structural bytes for receiver, amount, optional
memo, and required message; each decoded value uses its own established bound and the object has
one aggregate structural-whitespace allowance. -/
def maxJsonFtTransferCallWhitespace : Nat := 32
def maxJsonFtTransferCallInputBytes : Nat :=
  49 + 64 * 6 + 39 * 6 + 16 * 6 + 64 * 6 + maxJsonFtTransferCallWhitespace

/-- Exact largest receiver callback wire: `sender_id`, quoted amount, and required message use 37
structural bytes; each decoded value has its own worst-case six-byte escape geometry. -/
def maxJsonFtOnTransferWhitespace : Nat := 32
def maxJsonFtOnTransferInputBytes : Nat :=
  37 + 64 * 6 + 39 * 6 + 64 * 6 + maxJsonFtOnTransferWhitespace

/-- Exact largest private resolver-shaped wire: 45 structural bytes for two AccountIds and one
quoted amount, two 64-byte ids and 39 digits each worst-case escaped, plus aggregate whitespace. -/
def maxJsonFtResolveWhitespace : Nat := 32
def maxJsonFtResolveInputBytes : Nat :=
  45 + 2 * 64 * 6 + 39 * 6 + maxJsonFtResolveWhitespace

/-- Exact largest storage-deposit-shaped wire: the string-account and `false` boolean form has
43 structural bytes, with the established AccountId escape and aggregate whitespace bounds. -/
def maxJsonStorageDepositWhitespace : Nat := 32
def maxJsonStorageDepositInputBytes : Nat :=
  43 + 64 * 6 + maxJsonStorageDepositWhitespace

/-- Exact largest storage-unregister-shaped wire: `{"force":false}` is 15 bytes, plus the
established aggregate structural-whitespace budget. -/
def maxJsonStorageUnregisterWhitespace : Nat := 32
def maxJsonStorageUnregisterInputBytes : Nat :=
  15 + maxJsonStorageUnregisterWhitespace

/-- Optional quoted-u128 storage-withdraw input has the same exact maximum string geometry as the
required amount object: `{"amount":""}` is 13 structural bytes, each of 39 decoded digits may be
one six-byte Unicode escape, and structural whitespace is independently bounded at 32 bytes. -/
def maxJsonStorageWithdrawWhitespace : Nat := 32
def maxJsonStorageWithdrawInputBytes : Nat :=
  13 + 39 * 6 + maxJsonStorageWithdrawWhitespace

def accountIdSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.AccountId" #[
    ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64),
    ("w4", .scalar .uint64), ("w5", .scalar .uint64),
    ("w6", .scalar .uint64), ("w7", .scalar .uint64)]

def optionalMemo16Schema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.OptionalMemo16" #[
    ("present", .scalar .uint64), ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64)]

def boundedMessage64Schema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.BoundedMessage64" #[
    ("length", .scalar .uint64),
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64),
    ("w4", .scalar .uint64), ("w5", .scalar .uint64),
    ("w6", .scalar .uint64), ("w7", .scalar .uint64)]

def ftTransferArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.FtTransferArgs" #[
    ("receiverId", accountIdSchema), ("amount", .scalar .uint128),
    ("memo", optionalMemo16Schema)]

def ftTransferCallArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.FtTransferCallArgs" #[
    ("receiverId", accountIdSchema), ("amount", .scalar .uint128),
    ("memo", optionalMemo16Schema), ("msg", boundedMessage64Schema)]

def ftOnTransferArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.FtOnTransferArgs" #[
    ("senderId", accountIdSchema), ("amount", .scalar .uint128),
    ("msg", boundedMessage64Schema)]

def ftResolveTransferArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.FtResolveTransferArgs" #[
    ("senderId", accountIdSchema), ("receiverId", accountIdSchema),
    ("amount", .scalar .uint128)]

def storageDepositArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.StorageDepositArgs" #[
    ("accountPresent", .scalar .uint64), ("accountId", accountIdSchema),
    ("registrationOnly", .scalar .uint64)]

def storageUnregisterArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.StorageUnregisterArgs" #[
    ("force", .scalar .uint64)]

def storageWithdrawArgsSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.StorageWithdrawArgs" #[
    ("amountPresent", .scalar .uint64), ("amount", .scalar .uint128)]

def jsonBooleanResultSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.JsonBooleanResult" #[
    ("value", .scalar .uint64)]

def base64Hash32ResultSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.Base64Hash32Result" #[
    ("w0", .scalar .uint64), ("w1", .scalar .uint64),
    ("w2", .scalar .uint64), ("w3", .scalar .uint64)]

def storageBalanceResultSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.StorageBalanceResult" #[
    ("registered", .scalar .uint64), ("total", .scalar .uint128),
    ("available", .scalar .uint128)]

def storageBalanceBoundsResultSchema : Core.Codec.Schema :=
  .record "ProofForge.Wasm.Near.Runtime.StorageBalanceBoundsResult" #[
    ("min", .scalar .uint128), ("hasMax", .scalar .uint64),
    ("max", .scalar .uint128)]

/-- Closed target input policies. The AccountId plan accepts one bounded one-field JSON object;
it is deliberately narrower than generic serde_json-generated method wrappers. -/
inductive InputPlan where
  | borsh (plan : BorshInputPlan)
  | noArgsIgnoreInput
  | jsonAccountId
  | jsonU128Amount
  | jsonOptionalMemo16
  | jsonMessage64
  | jsonFtTransferArgs
  | jsonFtTransferCallArgs
  | jsonFtOnTransferArgs
  | jsonFtResolveTransferArgs
  | jsonStorageDepositArgs
  | jsonStorageUnregisterArgs
  | jsonStorageWithdrawArgs
  deriving Repr, BEq, Inhabited

def InputPlan.localCount : InputPlan → Nat
  | .borsh plan => plan.localCount
  | .noArgsIgnoreInput => 0
  | .jsonAccountId => 9
  | .jsonU128Amount => 2
  | .jsonOptionalMemo16 => 4
  | .jsonMessage64 => 9
  | .jsonFtTransferArgs => 15
  | .jsonFtTransferCallArgs => 24
  | .jsonFtOnTransferArgs => 20
  | .jsonFtResolveTransferArgs => 20
  | .jsonStorageDepositArgs => 11
  | .jsonStorageUnregisterArgs => 1
  | .jsonStorageWithdrawArgs => 3

def InputPlan.canonical : InputPlan → String
  | .borsh plan => plan.canonical
  | .noArgsIgnoreInput => "near-no-args-ignore-input-v1"
  | .jsonAccountId =>
      s!"near-json-account-id-object-bounded-v1(max-wire={maxJsonAccountInputBytes}," ++
        s!"ws={maxJsonAccountWhitespace},keys=canonical,unknown=reject)"
  | .jsonU128Amount =>
      s!"near-json-u128-amount-object-canonical-v1(max-wire={maxJsonU128InputBytes}," ++
        s!"ws={maxJsonU128Whitespace},digits=1..39,unknown=reject)"
  | .jsonOptionalMemo16 =>
      s!"near-json-optional-memo16-object-canonical-v1(max-wire={maxJsonMemoInputBytes}," ++
        s!"ws={maxJsonMemoWhitespace},decoded-bytes=0..16,unknown=reject)"
  | .jsonMessage64 =>
      s!"near-json-message64-object-canonical-v1(max-wire={maxJsonMessageInputBytes}," ++
        s!"ws={maxJsonMessageWhitespace},decoded-bytes=0..64,unknown=reject)"
  | .jsonFtTransferArgs =>
      s!"near-json-ft-transfer-args-bounded-v1(max-wire={maxJsonFtTransferInputBytes}," ++
        s!"ws={maxJsonFtTransferWhitespace},order=any,keys=raw,unknown=reject)"
  | .jsonFtTransferCallArgs =>
      s!"near-json-ft-transfer-call-args-bounded-v1(max-wire={maxJsonFtTransferCallInputBytes}," ++
        s!"ws={maxJsonFtTransferCallWhitespace},order=any,keys=raw,unknown=reject)"
  | .jsonFtOnTransferArgs =>
      s!"near-json-ft-on-transfer-args-bounded-v1(max-wire={maxJsonFtOnTransferInputBytes}," ++
        s!"ws={maxJsonFtOnTransferWhitespace},order=any,keys=raw,unknown=reject)"
  | .jsonFtResolveTransferArgs =>
      s!"near-json-ft-resolve-args-bounded-v1(max-wire={maxJsonFtResolveInputBytes}," ++
        s!"ws={maxJsonFtResolveWhitespace},order=any,keys=raw,unknown=reject)"
  | .jsonStorageDepositArgs =>
      s!"near-json-storage-deposit-args-bounded-v1(max-wire={maxJsonStorageDepositInputBytes}," ++
        s!"ws={maxJsonStorageDepositWhitespace},order=any,keys=raw,unknown=reject)"
  | .jsonStorageUnregisterArgs =>
      s!"near-json-storage-unregister-args-bounded-v1(max-wire={maxJsonStorageUnregisterInputBytes}," ++
        s!"ws={maxJsonStorageUnregisterWhitespace},keys=raw,unknown=reject)"
  | .jsonStorageWithdrawArgs =>
      s!"near-json-storage-withdraw-args-bounded-v1(max-wire={maxJsonStorageWithdrawInputBytes}," ++
        s!"ws={maxJsonStorageWithdrawWhitespace},digits=1..39,keys=raw,unknown=reject)"

def targetInputPlan (schema : Core.Codec.Schema) : Except String InputPlan := do
  if schema == accountIdSchema then return .jsonAccountId
  if schema == .scalar .uint128 then return .jsonU128Amount
  if schema == optionalMemo16Schema then return .jsonOptionalMemo16
  if schema == boundedMessage64Schema then return .jsonMessage64
  if schema == ftTransferArgsSchema then return .jsonFtTransferArgs
  if schema == ftTransferCallArgsSchema then return .jsonFtTransferCallArgs
  if schema == ftOnTransferArgsSchema then return .jsonFtOnTransferArgs
  if schema == ftResolveTransferArgsSchema then return .jsonFtResolveTransferArgs
  if schema == storageDepositArgsSchema then return .jsonStorageDepositArgs
  if schema == storageUnregisterArgsSchema then return .jsonStorageUnregisterArgs
  if schema == storageWithdrawArgsSchema then return .jsonStorageWithdrawArgs
  match schema with
  | .boundedBytes capacity => .borsh <$> inputPlan (.boundedBytes capacity)
  | .boundedString capacity => .borsh <$> inputPlan (.boundedString capacity)
  | _ => throw "near/codec: unsupported specialized input schema"

/-- Keep fixed return frames small enough for deterministic generated WAT. This is a compiler
resource bound, not a Borsh or nearcore wire limit. -/
def maxBoundedOutputCapacity : Nat := 64

inductive BorshOutputKind where
  | array
  | bytes
  | string
  deriving Repr, BEq, Inhabited

/-- Target-owned output geometry. Extract supplies `length, slot₀ … slotₙ₋₁`; the emitter publishes
only canonical `u32_le(length) || active elements` through invocation-local arena memory. -/
structure BorshOutputPlan where
  kind : BorshOutputKind
  capacity : Nat
  elementWidth : Nat
  validateUtf8 : Bool
  deriving Repr, BEq, Inhabited

def BorshOutputPlan.sourceValueCount (plan : BorshOutputPlan) : Nat :=
  1 + plan.capacity

def BorshOutputPlan.maxBytes (plan : BorshOutputPlan) : Nat :=
  4 + plan.capacity * plan.elementWidth

def BorshOutputPlan.canonical (plan : BorshOutputPlan) : String :=
  let kind := match plan.kind with
    | .array => "array"
    | .bytes => "bytes"
    | .string => "string"
  s!"near-borsh-output-{kind}-v1(capacity={plan.capacity},width={plan.elementWidth})"

def outputPlan : Core.Codec.Schema → Except String BorshOutputPlan
  | .boundedArray capacity (.scalar (.uint bits)) => do
      let width := bits / 8
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      unless bits % 8 == 0 && (width == 1 || width == 2 || width == 4 || width == 8) do
        throw "near/codec: bounded output elements must be UInt8, UInt16, UInt32, or UInt64"
      pure { kind := .array, capacity, elementWidth := width, validateUtf8 := false }
  | .boundedBytes capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      pure { kind := .bytes, capacity, elementWidth := 1, validateUtf8 := false }
  | .boundedString capacity => do
      unless 1 ≤ capacity && capacity ≤ maxBoundedOutputCapacity do
        throw s!"near/codec: bounded output capacity must be in 1..{maxBoundedOutputCapacity}"
      pure { kind := .string, capacity, elementWidth := 1, validateUtf8 := true }
  | .boundedArray .. =>
      throw "near/codec: bounded output elements must be UInt8, UInt16, UInt32, or UInt64"
  | _ => throw "near/codec: output plan requires bounded bytes, string, or scalar array"

/-- Closed NEAR output policies. JSON support is limited to quoted u128 scalar results, exact
compiler-owned Boolean/StorageBalance/StorageBalanceBounds frames, and explicit Unit mutation
results; generic objects, arrays, nullable values, and strings remain absent. -/
inductive OutputPlan where
  | borsh (plan : BorshOutputPlan)
  | jsonU128
  | promiseOrJsonU128
  | jsonStorageBalanceOption
  | jsonStorageBalanceBounds
  | jsonBase64Hash32
  | jsonBoolean
  | jsonNullUnit
  | voidEmpty
  deriving Repr, BEq, Inhabited

def OutputPlan.sourceValueCount : OutputPlan → Nat
  | .borsh plan => plan.sourceValueCount
  | .jsonU128 => 2
  | .promiseOrJsonU128 => 2
  | .jsonStorageBalanceOption => 5
  | .jsonStorageBalanceBounds => 5
  | .jsonBase64Hash32 => 4
  | .jsonBoolean => 1
  | .jsonNullUnit => 0
  | .voidEmpty => 0

def OutputPlan.canonical : OutputPlan → String
  | .borsh plan => plan.canonical
  | .jsonU128 => "near-json-u128-string-v1"
  | .promiseOrJsonU128 => "near-promise-or-json-u128-v1"
  | .jsonStorageBalanceOption => "near-json-storage-balance-option-v1"
  | .jsonStorageBalanceBounds => "near-json-storage-balance-bounds-v1"
  | .jsonBase64Hash32 => "near-json-base64-hash32-v1"
  | .jsonBoolean => "near-json-boolean-v1"
  | .jsonNullUnit => "near-json-null-unit-v1"
  | .voidEmpty => "near-void-empty-v1"

/-- Select only target-owned outputs already represented by exact fixed extractor frames. -/
def targetOutputPlan : Core.Codec.Schema → Except String OutputPlan
  | .boundedArray capacity element => .borsh <$> outputPlan (.boundedArray capacity element)
  | .boundedBytes capacity => .borsh <$> outputPlan (.boundedBytes capacity)
  | .boundedString capacity => .borsh <$> outputPlan (.boundedString capacity)
  | .scalar .uint128 => pure .jsonU128
  | schema =>
      if schema == storageBalanceResultSchema then pure .jsonStorageBalanceOption
      else if schema == storageBalanceBoundsResultSchema then pure .jsonStorageBalanceBounds
      else if schema == base64Hash32ResultSchema then pure .jsonBase64Hash32
      else if schema == jsonBooleanResultSchema then pure .jsonBoolean
      else if schema == .unit then pure .jsonNullUnit
      else throw "near/codec: unsupported specialized output schema"

end ProofForge.Wasm.Near.Codec
