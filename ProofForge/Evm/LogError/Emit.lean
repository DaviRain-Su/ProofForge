import ProofForge.Evm.LogError

namespace ProofForge.Evm.LogError.Emit

/-!
Sole interpreter for the typed LOG0..4 / custom-error plans (EVM-RT-2b).

`emitLog` is the only spelling of EVM event-log emission:

1. the ABI data words at `memory[wordOffset i)` (data always starts at offset 0), then
2. the `log0` … `log4` opcode named by `LogPlan.topicCount`, with data byte length
   `LogPlan.dataBytes` and the topic words in plan order.

`emitRevert` is the only spelling of ABI custom-error reverts:

1. the 4-byte selector left-aligned at `memory[0..3]` via `shl(224, ..)`,
2. the ABI argument words at `memory[argOffset i)`, then
3. `revert(0, revertBytes)`.

Plans carry already-materialized Yul words, so the interpreter allocates no fresh names and
threads no emitter state; the context is indentation only, which keeps branch-scoped emission
(permit's nested gates) byte-exact with the previous inline spellings. Malformed plans (more
than 4 topics, oversized data, a selector that is not exactly 4 bytes of lowercase hex,
oversized argument lists) fail closed with an `extract/unsupported` error instead of emitting.
-/

private def nl : String := "\n"

/-- Minimal emission context shared by component emitters: indentation only. Plans consume
already-materialized words, so no fresh-name or materialization state is required. -/
structure Context where
  indent : String

/-- Emit one validated LOG0..4 plan: data words at `memory[0, dataBytes)`, then the `logN`
opcode named by the topic count. -/
def emitLog (context : Context) (plan : LogPlan) : Except String String := do
  if !plan.wellFormed then
    throw "extract/unsupported: evm log plan shape"
  let indent := context.indent
  let mut txt := ""
  for i in [0:plan.data.size] do
    txt := txt ++ indent ++ "mstore(" ++ toString (LogPlan.wordOffset i) ++ ", " ++
      plan.data[i]! ++ ")" ++ nl
  let mut invoke := "log" ++ toString plan.topicCount ++ "(0, " ++ toString plan.dataBytes
  for topic in plan.topics do
    invoke := invoke ++ ", " ++ topic
  return txt ++ indent ++ invoke ++ ")" ++ nl

/-- Emit one validated custom-error plan: selector at `memory[0..3]`, argument words at
`memory[argOffset i)`, then `revert(0, revertBytes)`. -/
def emitRevert (context : Context) (plan : ErrorPlan) : Except String String := do
  if !plan.wellFormed then
    throw "extract/unsupported: evm error plan shape"
  let indent := context.indent
  let mut txt := indent ++ "mstore(0, shl(224, 0x" ++ plan.selector ++ "))" ++ nl
  for i in [0:plan.args.size] do
    txt := txt ++ indent ++ "mstore(" ++ toString (ErrorPlan.argOffset i) ++ ", " ++
      plan.args[i]! ++ ")" ++ nl
  return txt ++ indent ++ "revert(0, " ++ toString plan.revertBytes ++ ")" ++ nl

end ProofForge.Evm.LogError.Emit
