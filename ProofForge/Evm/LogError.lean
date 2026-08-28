namespace ProofForge.Evm.LogError

/-!
Target-local typed plan for EVM event-log and custom-error data (EVM-RT-2b).

This module is the plan layer of the shared LOG / custom-error policy. It names the memory
geometry that used to be inlined per effect site in `Evm.NativeFx.Emit` (and duplicated by
permit in `Evm.ClosedCall.Emit`):

- `LogPlan` — one LOG0..4 emission: the already-materialized ABI data words stored at
  `memory[wordOffset i)` (data always starts at memory offset 0) and the already-materialized
  topic words in order. `topicCount` names the `log0` … `log4` opcode and is bounded at
  `maxTopics = 4`; the data payload is bounded at `maxLogDataWords = 4` words (128 bytes).
- `ErrorPlan` — one ABI custom-error revert: the 4-byte `selector` (8 lowercase hex
  characters) stored left-aligned at `memory[0..3]`, the already-materialized ABI argument
  words stored at `memory[argOffset i)`, and the total revert length
  `revertBytes = 4 + 32 · |args|`, bounded at `maxErrorArgs = 4` words.

Plans consume already-materialized Yul words; they never materialize operands, allocate fresh
names, or open opcodes beyond the `log0..4` / `revert` pair. Closed semantic names (event
signatures such as `Transfer(address,address,uint256)`, error names such as
`Insufficient(uint256,uint256)`) stay owned by `Evm.NativeFx` / `Evm.ClosedCall`; this layer
validates shape only and fails closed on any shape it does not name. It is not a source API
for arbitrary event signatures or error selectors, and validating LOG0/2/4 shapes here does
not expose them to source contracts. `Evm.LogError.Emit` is the sole interpreter.
-/

/-- Bytes in one ABI word. -/
def abiWordBytes : Nat := 32

/-- Bytes in one ABI error selector. -/
def selectorBytes : Nat := 4

/-- Hardware bound on LOG topic count (LOG0..LOG4). -/
def maxTopics : Nat := 4

/-- Bound on LOG data payload: at most four ABI words (128 bytes) at memory offset 0. -/
def maxLogDataWords : Nat := 4

/-- Bound on custom-error ABI argument words. -/
def maxErrorArgs : Nat := 4

/-- Typed plan for one LOG0..4 emission. `data` holds already-materialized ABI words stored at
`memory[wordOffset i)`; `topics` holds the already-materialized topic words in order (topic 0
is the event signature hash for named events). -/
structure LogPlan where
  data : Array String := #[]
  topics : Array String := #[]
  deriving BEq, Repr, Inhabited

/-- Memory offset of ABI data word `wordIndex`; data always starts at offset 0. -/
def LogPlan.wordOffset (wordIndex : Nat) : Nat := abiWordBytes * wordIndex

/-- Topic count naming the `log0` … `log4` opcode. -/
def LogPlan.topicCount (plan : LogPlan) : Nat := plan.topics.size

/-- Data byte length emitted at memory offset 0. -/
def LogPlan.dataBytes (plan : LogPlan) : Nat := abiWordBytes * plan.data.size

/-- Fail-closed shape gate: at most `maxTopics` topics and at most `maxLogDataWords` data
words. -/
def LogPlan.wellFormed (plan : LogPlan) : Bool :=
  plan.topicCount ≤ maxTopics && plan.data.size ≤ maxLogDataWords

/-- Typed plan for one ABI custom-error revert. `selector` is the 4-byte error selector as 8
lowercase hex characters; `args` holds the already-materialized ABI argument words in order. -/
structure ErrorPlan where
  selector : String
  args : Array String := #[]
  deriving BEq, Repr, Inhabited

/-- Memory offset of ABI argument word `argIndex`; argument data starts after the selector. -/
def ErrorPlan.argOffset (argIndex : Nat) : Nat := selectorBytes + abiWordBytes * argIndex

/-- Total revert byte length: selector plus ABI argument words. -/
def ErrorPlan.revertBytes (plan : ErrorPlan) : Nat :=
  selectorBytes + abiWordBytes * plan.args.size

private def isLowerHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Fail-closed shape gate: the selector is exactly 4 bytes of lowercase hex and argument
words stay within `maxErrorArgs`. -/
def ErrorPlan.wellFormed (plan : ErrorPlan) : Bool :=
  plan.selector.length == 2 * selectorBytes && plan.selector.all isLowerHexDigit &&
    plan.args.size ≤ maxErrorArgs

end ProofForge.Evm.LogError
