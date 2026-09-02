import ProofForge.Svm.SemanticsBridge
import ProofForge.Svm.EmitCompat
import ProofForge.Svm.IRCompat
import ProofForge.Extract.LegacyGolden

/-!
# Tests/SemanticsSpec

**通用语义差分**：Golden 合约 → 发射器 `.s` → `assembleSf`（解析器）
→ SbpfSemantics 小步执行机 → 观察。覆盖 dispatcher / 账户预检 /
状态读写 / return data，全链路 kernel 验证。
-/

open SbpfSemantics

namespace Tests.SemanticsSpec

open ProofForge.Svm.SemanticsBridge

private def leNat (n : Nat) : Array UInt8 :=
  (List.range 8).toArray.map
    (fun i => UInt8.ofNat ((n >>> (8 * i)) &&& 0xff))

private def leU64 (w : UInt64) : Array UInt8 := leNat w.toNat

/-- Golden Counter 发射文本（与 CI 提取路径同源）。 -/
private def counterAsm : Except String String :=
  ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCounter

/-- 发射文本 → L2 程序（指令数）。 -/
private def counterParsed : Except String Nat := do
  let asm ← counterAsm
  let P ← assembleSf asm
  .ok P.size

private theorem counter_asm_parses_impl :
    (match counterParsed with | .ok n => 400 ≤ n && n ≤ 600 | .error _ => false) = true := by
  native_decide

/-- 指令 discriminator：与 `Svm.ABI.discHexOf` 同源（LE 字节序）。 -/
private def discBytes (ixName : String) (n : Nat) : Array UInt8 :=
  leNat (ProofForge.Crypto.Sha256.first8Le
    (ProofForge.Svm.ABI.discPreimage ixName n)).toNat

/-- Golden Counter 的 StateCell 布局标记（`0x…` 十六进制）。 -/
private def counterMarkerHex : Except String String :=
  match ProofForge.Svm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error e => .error e
  | .ok ir => ProofForge.Svm.IR.layoutMarkerHex ir

private def mkIx (ixName : String) (args : Array UInt64) : Array UInt8 :=
  (discBytes ixName args.size) ++
    (args.map (fun w => leU64 w)).foldl (fun acc w => acc ++ w) #[]

/-! 三笔连续调用（同一记忆）：init(5) → increment(3) → get。
观察 return data（LE 编码的状态字）。 -/

private def counterSeq
    : Except String (Array UInt8 × SbpfSemantics.Word × Array UInt8 × SbpfSemantics.Word × Array UInt8) := do
  let asm ← counterAsm
  let P ← assembleSf asm
  let ir ← match ProofForge.Svm.IR.fromProgram ProofForge.Golden.extractedCounter with
    | .ok p => .ok p
    | .error e => .error e
  -- 布局 marker：与发射器同源（`ABI.layoutMarkerHexOf` = first8Be 的 u64Hex，
  -- 大端写法；账户里的 marker 字是 LE 编码，所以先取 u64 再编 LE 字节）。
  let markerHex ← ProofForge.Svm.IR.layoutMarkerHex ir
  let markerW : Word ←
    match numInt? markerHex.toList with
    | some v => .ok (BitVec.ofNat 64 v.toNat)
    | none => .error "semanticsBridge: bad marker hex"
  let markerBytes : Array UInt8 := le64Bytes markerW
  -- init：data 全零（未初始化账态）
  let (m1, o1) ← runSfInitial? asm
    { ix := mkIx "initialize" #[5], data := Array.replicate 16 0 } 4096
  -- increment(3)：账户数据 = [marker][5]
  let data1 : Array UInt8 := markerBytes ++ (leU64 5)
  let (m2, o2) ← runSfNext? asm P m1 { ix := mkIx "increment" #[3], data := data1 } 4096
  -- get
  let (_m3, o3) ← runSfNext? asm P m2
    { ix := mkIx "get" #[], data := markerBytes ++ (leU64 8) } 4096
  .ok (o1.returnData, o2.r0, o2.returnData, o3.r0, o3.returnData)

/-- fail-closed：畸形 discriminator（全 0）走 `err_unknown_disc`，r0 = 1。 -/
private def counterBadDisc : Except String SbpfSemantics.Word := do
  let asm ← counterAsm
  let (_m, o) ← runSfInitial? asm
    { ix := Array.replicate 16 0, data := Array.replicate 16 0 } 4096
  .ok o.r0

private theorem counter_unknown_disc_fails_closed :
    (match counterBadDisc with | .ok w => w == 1#64 | .error _ => false) = true := by
  native_decide

/-- init 不发布 return data（合约语义：只写账户）；increment(3) 与 get
均发布 LE(8)；三笔均正常退出（r0 = 0）。 -/
private theorem counter_seq_matches_model :
    (match counterSeq with
      | .ok (a, r02, b, r03, c) => a == #[] && b == leU64 8 && c == leU64 8 && r02 == 0 && r03 == 0
      | .error _ => false) = true := by
  native_decide


/-! ## E2 corpus gate (`svm-sem-002`)

Named parse sweep: every Golden program that emits must parse. The first failure
string includes the program name so CI logs localize the culprit.

Window (two-cell container) adds a second step golden beside Counter.
-/

/-- First failing Golden program name, or `none` when the emit→parse corpus is green. -/
private def firstGoldenParseFailure : Option String :=
  ProofForge.Golden.programs.foldl
    (fun acc p =>
      match acc with
      | some _ => acc
      | none =>
          match ProofForge.Svm.Emit.emitCounterAsm p with
          | .error _ => none  -- emitter fail-closed skip (EVM leaf / unsupported)
          | .ok asm =>
              match assembleSf asm with
              | .ok _ => none
              | .error e => some s!"{p.name}: {e.take 120}")
    none

private def allGoldenParseOk : Bool := firstGoldenParseFailure.isNone

private theorem golden_corpus_parses : allGoldenParseOk = true := by
  native_decide

/-- Window emit text (Golden fixture; two-cell container). -/
private def windowAsm : Except String String :=
  match ProofForge.Golden.programs.find? (·.name == "Window") with
  | some p => ProofForge.Svm.Emit.emitCounterAsm p
  | none => .error "semantics: Window golden missing"

private def windowParsed : Except String Nat := do
  let asm ← windowAsm
  let P ← assembleSf asm
  .ok P.size

private theorem window_asm_parses_impl :
    (match windowParsed with | .ok n => 100 ≤ n && n ≤ 300 | .error _ => false) = true := by
  native_decide

private def windowMarkerHex : Except String String := do
  let some p := ProofForge.Golden.programs.find? (·.name == "Window")
    | .error "semantics: Window golden missing"
  let ir ← match ProofForge.Svm.IR.fromProgram p with
    | .ok p => .ok p
    | .error e => .error e
  ProofForge.Svm.IR.layoutMarkerHex ir

/-- Window: initialize(7) → setTail(9) → getHead. Head stays 7; both mutations exit r0=0. -/
private def windowSeq
    : Except String (Array UInt8 × SbpfSemantics.Word × Array UInt8 × SbpfSemantics.Word × Array UInt8) := do
  let asm ← windowAsm
  let P ← assembleSf asm
  let markerHex ← windowMarkerHex
  let markerW : Word ←
    match numInt? markerHex.toList with
    | some v => .ok (BitVec.ofNat 64 v.toNat)
    | none => .error "semanticsBridge: bad Window marker hex"
  let markerBytes : Array UInt8 := le64Bytes markerW
  let (m1, o1) ← runSfInitial? asm
    { ix := mkIx "initialize" #[7], data := Array.replicate 24 0 } 4096
  let data1 : Array UInt8 := markerBytes ++ leU64 7 ++ leU64 0
  let (m2, o2) ← runSfNext? asm P m1 { ix := mkIx "setTail" #[9], data := data1 } 4096
  let (_m3, o3) ← runSfNext? asm P m2
    { ix := mkIx "getHead" #[], data := markerBytes ++ leU64 7 ++ leU64 9 } 4096
  .ok (o1.returnData, o2.r0, o2.returnData, o3.r0, o3.returnData)

private theorem window_seq_matches_model :
    (match windowSeq with
      | .ok (a, r02, b, r03, c) =>
          a == #[] && b == leU64 9 && c == leU64 7 && r02 == 0 && r03 == 0
      | .error _ => false) = true := by
  native_decide

end Tests.SemanticsSpec
