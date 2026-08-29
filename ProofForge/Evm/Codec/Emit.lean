import ProofForge.Evm.Codec

namespace ProofForge.Evm.Codec.Emit

private def nl : String := "\n"
private def revert0 : String := "revert(0, 0)"

/-- Render canonical padding/range checks for one standard-ABI word. -/
def renderWordGuard (indent name : String) (type : Core.Codec.Scalar) :
    Except String String := do
  match ← Codec.wordGuard type with
  | .fullWord => return ""
  | .boolean =>
      return indent ++ "if gt(" ++ name ++ ", 1) { " ++ revert0 ++ " }" ++ nl
  | .unsignedMax bits =>
      return indent ++ "if gt(" ++ name ++ ", " ++ Codec.byteMask (bits / 8) ++
        ") { " ++ revert0 ++ " }" ++ nl
  | .address160 =>
      return indent ++ "if gt(" ++ name ++ ", " ++ Codec.byteMask 20 ++
        ") { " ++ revert0 ++ " }" ++ nl
  | .fixedBytesLeftPadded bytes =>
      return indent ++ "if and(" ++ name ++ ", " ++ Codec.byteMask (32 - bytes) ++
        ") { " ++ revert0 ++ " }" ++ nl

/-- Interpret fixed Tagged Tuple v1 guards from the codec plan. This is independent of contract
Ops and storage: it only constrains already decoded input locals. -/
def renderTaggedGuards (indent argPrefix : String)
    (plans : Array Codec.AbiInputPlan) : Except String String := do
  let mut out := ""
  let mut base := 0
  for plan in plans do
    for guard in plan.taggedGuards do
      unless guard.tagWord < plan.wordCount &&
          guard.payloadStart + guard.payloadWords ≤ plan.wordCount &&
          !guard.activePayloadWords.isEmpty &&
          guard.activePayloadWords.all (· ≤ guard.payloadWords) do
        throw "evm/codec: malformed tagged tuple v1 guard"
      let tag := argPrefix ++ toString (base + guard.tagWord)
      out := out ++ indent ++ "if iszero(lt(" ++ tag ++ ", " ++
        toString guard.activePayloadWords.size ++ ")) { " ++ revert0 ++ " }" ++ nl
      for variant in [0:guard.activePayloadWords.size] do
        let active := guard.activePayloadWords[variant]!
        for lane in [active:guard.payloadWords] do
          let payload := argPrefix ++ toString (base + guard.payloadStart + lane)
          out := out ++ indent ++ "if and(eq(" ++ tag ++ ", " ++ toString variant ++
            "), " ++ payload ++ ") { " ++ revert0 ++ " }" ++ nl
    base := base + plan.wordCount
  return out

/-- Render one strict Unicode-scalar UTF-8 scanner over a target-owned byte accessor. Input
calldata and output memory supply different accessors without duplicating the validation policy. -/
private def renderUtf8Guard (namePrefix indent lengthName : String)
    (byteAt : String → String) (index : Nat) : String :=
  let i := namePrefix ++ "i" ++ toString index
  let need := namePrefix ++ "need" ++ toString index
  let min := namePrefix ++ "min" ++ toString index
  let max := namePrefix ++ "max" ++ toString index
  let byte := namePrefix ++ "byte" ++ toString index
  indent ++ "let " ++ i ++ " := 0" ++ nl ++
  indent ++ "let " ++ need ++ " := 0" ++ nl ++
  indent ++ "let " ++ min ++ " := 128" ++ nl ++
  indent ++ "let " ++ max ++ " := 191" ++ nl ++
  indent ++ "for { } lt(" ++ i ++ ", " ++ lengthName ++ ") { " ++ i ++
    " := add(" ++ i ++ ", 1) } {" ++ nl ++
  indent ++ "  let " ++ byte ++ " := " ++ byteAt i ++ nl ++
  indent ++ "  switch " ++ need ++ nl ++
  indent ++ "  case 0 {" ++ nl ++
  indent ++ "    if gt(" ++ byte ++ ", 127) {" ++ nl ++
  indent ++ "      if or(lt(" ++ byte ++ ", 194), gt(" ++ byte ++ ", 244)) { " ++
    revert0 ++ " }" ++ nl ++
  indent ++ "      if lt(" ++ byte ++ ", 224) { " ++ need ++ " := 1 }" ++ nl ++
  indent ++ "      if and(gt(" ++ byte ++ ", 223), lt(" ++ byte ++ ", 240)) {" ++ nl ++
  indent ++ "        " ++ need ++ " := 2" ++ nl ++
  indent ++ "        if eq(" ++ byte ++ ", 224) { " ++ min ++ " := 160 }" ++ nl ++
  indent ++ "        if eq(" ++ byte ++ ", 237) { " ++ max ++ " := 159 }" ++ nl ++
  indent ++ "      }" ++ nl ++
  indent ++ "      if gt(" ++ byte ++ ", 239) {" ++ nl ++
  indent ++ "        " ++ need ++ " := 3" ++ nl ++
  indent ++ "        if eq(" ++ byte ++ ", 240) { " ++ min ++ " := 144 }" ++ nl ++
  indent ++ "        if eq(" ++ byte ++ ", 244) { " ++ max ++ " := 143 }" ++ nl ++
  indent ++ "      }" ++ nl ++
  indent ++ "    }" ++ nl ++
  indent ++ "  }" ++ nl ++
  indent ++ "  default {" ++ nl ++
  indent ++ "    if or(lt(" ++ byte ++ ", " ++ min ++ "), gt(" ++ byte ++ ", " ++
    max ++ ")) { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "    " ++ need ++ " := sub(" ++ need ++ ", 1)" ++ nl ++
  indent ++ "    " ++ min ++ " := 128" ++ nl ++
  indent ++ "    " ++ max ++ " := 191" ++ nl ++
  indent ++ "  }" ++ nl ++
  indent ++ "}" ++ nl ++
  indent ++ "if " ++ need ++ " { " ++ revert0 ++ " }" ++ nl

/-- Interpret EVM input plans into one fixed local frame. Static values load from the top-level
head. Dynamic plans require canonical contiguous tails, cap their runtime length, zero inactive
locals, and validate packed bytes or every active array word before contract CFG execution. -/
def renderEntryArgs (plans : Array Codec.AbiInputPlan)
    (paramTypes : Array Core.Codec.Scalar) : Except String String := do
  let localWords := plans.foldl (init := 0) fun count plan => count + plan.wordCount
  unless localWords == paramTypes.size do
    throw "evm/codec: input plan local frame does not match parameter metadata"
  let headWords := plans.foldl (init := 0) fun count plan => count + plan.headWordCount
  let headBytes := headWords * 32
  let hasDynamic := plans.any (·.dynamic.isSome)
  let mut out := ""
  if hasDynamic then
    out := out ++
      "        if lt(calldatasize(), " ++ toString (4 + headBytes) ++ ") { " ++
        revert0 ++ " }" ++ nl ++
      "        let abi_size := sub(calldatasize(), 4)" ++ nl ++
      "        let abi_tail := " ++ toString headBytes ++ nl
  else
    out := out ++
      "        if iszero(eq(calldatasize(), " ++ toString (4 + headBytes) ++ ")) { " ++
        revert0 ++ " }" ++ nl
  let mut headWord := 0
  let mut localWord := 0
  let mut dynamicIndex := 0
  for plan in plans do
    match plan.dynamic with
    | none =>
        for i in [0:plan.wordCount] do
          let localIndex := localWord + i
          out := out ++
            "        let arg" ++ toString localIndex ++ " := calldataload(" ++
              toString (4 + (headWord + i) * 32) ++ ")" ++ nl
          let some type := paramTypes[localIndex]?
            | throw s!"evm/codec: missing entry parameter metadata at {localIndex}"
          out := out ++ (← renderWordGuard "        " ("arg" ++ toString localIndex) type)
        headWord := headWord + plan.wordCount
        localWord := localWord + plan.wordCount
    | some (.boundedArray array) =>
        let elementWords := array.elementWords.size
        unless 0 < elementWords &&
            plan.wordCount == 1 + array.capacity * elementWords &&
            plan.words[0]? == some .uint32 do
          throw "evm/codec: malformed bounded array v1 input plan"
        let dataName := "abi_data" ++ toString dynamicIndex
        let lengthName := "arg" ++ toString localWord
        out := out ++
          "        if iszero(eq(calldataload(" ++ toString (4 + headWord * 32) ++
            "), abi_tail)) { " ++ revert0 ++ " }" ++ nl ++
          "        let " ++ dataName ++ " := abi_tail" ++ nl ++
          "        if gt(add(" ++ dataName ++ ", 32), abi_size) { " ++ revert0 ++ " }" ++ nl ++
          "        let " ++ lengthName ++ " := calldataload(add(4, " ++ dataName ++ "))" ++ nl ++
          "        if gt(" ++ lengthName ++ ", " ++ toString array.capacity ++ ") { " ++
            revert0 ++ " }" ++ nl
        for i in [1:plan.wordCount] do
          out := out ++ "        let arg" ++ toString (localWord + i) ++ " := 0" ++ nl
        let elementBytes := elementWords * 32
        out := out ++
          "        abi_tail := add(abi_tail, add(32, mul(" ++ lengthName ++ ", " ++
            toString elementBytes ++ ")))" ++ nl ++
          "        if gt(abi_tail, abi_size) { " ++ revert0 ++ " }" ++ nl
        for elementIndex in [0:array.capacity] do
          out := out ++ "        if gt(" ++ lengthName ++ ", " ++ toString elementIndex ++
            ") {" ++ nl
          for wordIndex in [0:elementWords] do
            let relative := 1 + elementIndex * elementWords + wordIndex
            let localIndex := localWord + relative
            let dataOffset := 32 + (elementIndex * elementWords + wordIndex) * 32
            out := out ++
              "          arg" ++ toString localIndex ++ " := calldataload(add(add(4, " ++
                dataName ++ "), " ++ toString dataOffset ++ "))" ++ nl
            let some type := paramTypes[localIndex]?
              | throw s!"evm/codec: missing bounded element metadata at {localIndex}"
            out := out ++ (← renderWordGuard "          " ("arg" ++ toString localIndex) type)
          out := out ++ "        }" ++ nl
        headWord := headWord + 1
        localWord := localWord + plan.wordCount
        dynamicIndex := dynamicIndex + 1
    | some (.packedBytes bytes) =>
        unless plan.wordCount == 1 + bytes.capacity && plan.words[0]? == some .uint32 &&
            plan.words.extract 1 plan.wordCount == Array.replicate bytes.capacity .uint8 do
          throw "evm/codec: malformed packed bytes v1 input plan"
        let dataName := "abi_data" ++ toString dynamicIndex
        let lengthName := "arg" ++ toString localWord
        let paddedName := "abi_padded" ++ toString dynamicIndex
        let paddingIndex := "abi_padding_i" ++ toString dynamicIndex
        out := out ++
          "        if iszero(eq(calldataload(" ++ toString (4 + headWord * 32) ++
            "), abi_tail)) { " ++ revert0 ++ " }" ++ nl ++
          "        let " ++ dataName ++ " := abi_tail" ++ nl ++
          "        if gt(add(" ++ dataName ++ ", 32), abi_size) { " ++ revert0 ++ " }" ++ nl ++
          "        let " ++ lengthName ++ " := calldataload(add(4, " ++ dataName ++ "))" ++ nl ++
          "        if gt(" ++ lengthName ++ ", " ++ toString bytes.capacity ++ ") { " ++
            revert0 ++ " }" ++ nl
        for i in [1:plan.wordCount] do
          out := out ++ "        let arg" ++ toString (localWord + i) ++ " := 0" ++ nl
        out := out ++
          "        let " ++ paddedName ++ " := and(add(" ++ lengthName ++
            ", 31), not(31))" ++ nl ++
          "        abi_tail := add(abi_tail, add(32, " ++ paddedName ++ "))" ++ nl ++
          "        if gt(abi_tail, abi_size) { " ++ revert0 ++ " }" ++ nl ++
          "        for { let " ++ paddingIndex ++ " := " ++ lengthName ++ " } lt(" ++
            paddingIndex ++ ", " ++ paddedName ++ ") { " ++ paddingIndex ++ " := add(" ++
            paddingIndex ++ ", 1) } {" ++ nl ++
          "          if byte(0, calldataload(add(add(add(4, " ++ dataName ++ "), 32), " ++
            paddingIndex ++ "))) { " ++ revert0 ++ " }" ++ nl ++
          "        }" ++ nl
        if bytes.validateUtf8 then
          out := out ++ renderUtf8Guard "abi_utf8_" "        " lengthName (fun i =>
            "byte(0, calldataload(add(add(add(4, " ++ dataName ++ "), 32), " ++ i ++ ")))"
          ) dynamicIndex
        for i in [0:bytes.capacity] do
          out := out ++ "        if gt(" ++ lengthName ++ ", " ++ toString i ++ ") {" ++ nl ++
            "          arg" ++ toString (localWord + 1 + i) ++
              " := byte(0, calldataload(add(add(add(4, " ++ dataName ++ "), 32), " ++
              toString i ++ ")))" ++ nl ++
            "        }" ++ nl
        headWord := headWord + 1
        localWord := localWord + plan.wordCount
        dynamicIndex := dynamicIndex + 1
  if hasDynamic then
    out := out ++ "        if iszero(eq(abi_size, abi_tail)) { " ++ revert0 ++ " }" ++ nl
  return out

/-- Generic bridge from the target codec interpreter to the main CFG value materializer. Dynamic
result policy stays in this module; the main emitter supplies only source-value evaluation. -/
structure ReturnContext (Value State : Type) where
  indent : String
  materialize : String → Value → State → Except String (String × String × State)

/-- Interpret one bounded dynamic output plan. The fixed source frame is never returned directly:
the encoder emits the canonical ABI offset/length header and only the active array or byte prefix. -/
def renderDynamicReturn [Inhabited Value] (context : ReturnContext Value State)
    (plan : Codec.DynamicOutputPlan) (values : Array Value) (state : State) :
    Except String (String × State) := do
  let indent := context.indent
  unless values.size == plan.sourceWords.size do
    throw s!"evm/codec: dynamic result has {values.size} source parts, expected {plan.sourceWords.size}"
  let (lengthPre, length, state0) ← context.materialize indent values[0]! state
  let mut state := state0
  let mut out := lengthPre ++
    indent ++ "mstore(0, 32)" ++ nl ++
    indent ++ "mstore(32, " ++ length ++ ")" ++ nl
  match plan with
  | .boundedArray array =>
      unless array.elementWords.size == 1 do
        throw "evm/codec: malformed bounded array output plan"
      out := out ++ indent ++ "if gt(" ++ length ++ ", " ++ toString array.capacity ++
        ") { " ++ revert0 ++ " }" ++ nl
      for i in [0:array.capacity] do
        out := out ++ indent ++ "if gt(" ++ length ++ ", " ++ toString i ++ ") {" ++ nl
        let (pre, value, next) ←
          context.materialize (indent ++ "  ") values[1 + i]! state
        state := next
        out := out ++ pre ++ indent ++ "  mstore(" ++ toString (64 + i * 32) ++
          ", " ++ value ++ ")" ++ nl ++ indent ++ "}" ++ nl
      out := out ++ indent ++ "return(0, add(64, mul(" ++ length ++ ", 32)))" ++ nl
  | .packedBytes bytes =>
      out := out ++ indent ++ "if gt(" ++ length ++ ", " ++ toString bytes.capacity ++
        ") { " ++ revert0 ++ " }" ++ nl
      for word in [0:(bytes.capacity + 31) / 32] do
        out := out ++ indent ++ "mstore(" ++ toString (64 + word * 32) ++ ", 0)" ++ nl
      for i in [0:bytes.capacity] do
        out := out ++ indent ++ "if gt(" ++ length ++ ", " ++ toString i ++ ") {" ++ nl
        let (pre, value, next) ←
          context.materialize (indent ++ "  ") values[1 + i]! state
        state := next
        out := out ++ pre ++ indent ++ "  mstore8(" ++ toString (64 + i) ++
          ", " ++ value ++ ")" ++ nl ++ indent ++ "}" ++ nl
      if bytes.validateUtf8 then
        out := out ++ renderUtf8Guard "abi_ret_utf8_" indent length
          (fun i => "byte(0, mload(add(64, " ++ i ++ ")))") 0
      let padded := "abi_ret_padded"
      out := out ++ indent ++ "let " ++ padded ++ " := and(add(" ++ length ++
        ", 31), not(31))" ++ nl ++
        indent ++ "return(0, add(64, " ++ padded ++ "))" ++ nl
  return (out, state)

end ProofForge.Evm.Codec.Emit
