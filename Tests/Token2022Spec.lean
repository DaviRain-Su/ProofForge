import Examples.Token2022

namespace Tests.Token2022Spec

open Lean Elab Command
open Examples.Token2022
open ProofForge.Svm
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard token2022TransferChecked 7 6 == 0

#guard
  match send (init 0) 9 with
  | .ok (state, returned) => state.dummy == 0 && returned == 9
  | .error _ => false

elab "#pf_guard_token_2022_ir" : command => do
  let env ← getEnv
  let extracted ←
    match ProofForge.Extract.extractModuleIR env `Examples.Token2022 with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted extracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sendMethod := program.methods.find? (·.ixName == "send")
    | throwError "missing Token2022 send method"
  let expectedInvoke : IR.Op :=
    .invoke 4
      #[{ acc := 1, writable := true, accountData := some (.token2022Base .account) },
        { acc := 2, accountData := some (.token2022Base .mint) },
        { acc := 3, writable := true, accountData := some (.token2022Base .account) },
        { acc := 0, signer := true }]
      #[.u8le (.lit 12), .u64le (.arg 0), .u8le (.lit 6)] #[] none
  unless sendMethod.ops.contains expectedInvoke do
    throwError s!"Token-2022 constrained CPI was not retained: {repr sendMethod.ops}"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "; validate typed CPI account-data policies" &&
      asm.contains "jeq r2, 355, cpi_data_len_err_" &&
      asm.contains "jlt r2, 165, cpi_data_len_err_" &&
      asm.contains "jeq r2, 165, cpi_data_len_next_" &&
      asm.contains "jne r4, 1, cpi_data_len_err_" &&
      asm.contains "jne r4, 2, cpi_data_len_err_" &&
      asm.contains "call sol_invoke_signed_c" do
    throwError "Token-2022 bounded TLV preflight is missing from assembly"

#pf_guard_token_2022_ir

#guard ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 1, expectedDataLen := some 165 }

#guard !ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 1, expectedDataLen := some 18446744073709551616 }

#guard ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 2, accountData := some (.token2022Base .mint) }

#guard !ProofForge.Svm.Ops.CpiMeta.wellFormed
  { acc := 2, expectedDataLen := some 82, accountData := some (.token2022Base .mint) }

/-! ## Bounded TLV plan/interpreter gates -/

section TokenTlvGates
open ProofForge.Svm.Cpi.TokenTlv

/-- Byte-array-backed bounded view for host-side gates. -/
def gateView (bytes : Array UInt8) : View :=
  { dataLen := UInt64.ofNat bytes.size,
    readByte := fun off =>
      if off.toNat < bytes.size then some bytes[off.toNat]! else none }

/-- One little-endian `u16` header word. -/
def gateU16 (v : Nat) : Array UInt8 :=
  #[UInt8.ofNat (v % 256), UInt8.ofNat (v / 256)]

private def assertVerdict (plan : Plan) (accept? : UInt64 → Bool)
    (bytes : Array UInt8) (expected : Verdict) : Bool :=
  let view := gateView bytes
  -- Named `view` so it does not bind the optional `requiredBodyLen?` parameter.
  evaluate plan accept? (view := view) == expected && straightline plan view == expected

private def baseAccountBytes : Array UInt8 :=
  Array.range 165 |>.map (fun _ => (0 : UInt8))

private def baseMintBytes : Array UInt8 :=
  Array.range 82 |>.map (fun _ => (0 : UInt8))

private def mintPadding : Array UInt8 :=
  Array.range 83 |>.map (fun _ => (0 : UInt8))

private def extensionMint (typeByte : UInt8) (tlv : Array UInt8) : Array UInt8 :=
  baseMintBytes ++ mintPadding ++ #[typeByte] ++ tlv

private def extensionAccount (tlv : Array UInt8) : Array UInt8 :=
  baseAccountBytes ++ #[2] ++ tlv

-- The closed classifier's specialization equals the full bounded cursor on every gate.
#guard
  (assertVerdict accountPlan closedAccept? baseAccountBytes .accept &&
    assertVerdict mintPlan closedAccept? baseMintBytes .accept &&
    -- too short
    assertVerdict accountPlan closedAccept? (Array.range 164 |>.map (fun i => UInt8.ofNat (i % 7)))
      (.reject .tooShort) &&
    assertVerdict mintPlan closedAccept? (Array.range 81 |>.map (fun i => UInt8.ofNat (i % 7)))
      (.reject .tooShort) &&
    -- multisig-length ambiguity rejects before any base decode
    assertVerdict accountPlan closedAccept? (Array.range 355 |>.map (fun _ => (0 : UInt8)))
      (.reject .multisigLength) &&
    assertVerdict mintPlan closedAccept? (Array.range 355 |>.map (fun _ => (0 : UInt8)))
      (.reject .multisigLength) &&
    -- mint dead zone between its base span and the extension form
    assertVerdict mintPlan closedAccept? (Array.range 100 |>.map (fun _ => (0 : UInt8)))
      (.reject .tooShort) &&
    -- padding must stay zero
    assertVerdict mintPlan closedAccept?
      ((baseMintBytes ++ mintPadding ++ #[1] ++ #[0, 0, 0, 0]).set! 100 1)
      (.reject .paddingNotZero) &&
    -- wrong AccountType byte
    assertVerdict mintPlan closedAccept? (extensionMint 2 #[0, 0, 0, 0])
      (.reject .accountTypeMismatch) &&
    -- empty TLV region right after the type byte
    assertVerdict mintPlan closedAccept? (extensionMint 1 #[]) .accept &&
    -- single trailing byte tolerance
    assertVerdict accountPlan closedAccept? (baseAccountBytes ++ #[2] ++ #[7]) .accept &&
    -- short remainder 2..3: only Uninitialized(0) is official
    assertVerdict accountPlan closedAccept? (baseAccountBytes ++ #[2] ++ #[0, 0]) .accept &&
    assertVerdict accountPlan closedAccept? (baseAccountBytes ++ #[2] ++ #[0, 1])
      (.reject .truncatedHeader) &&
    -- full header with Uninitialized(0) type ends the region; later bytes are ignored
    assertVerdict accountPlan closedAccept?
      (baseAccountBytes ++ #[2] ++ gateU16 0 ++ #[9, 9, 9, 9]) .accept &&
    -- known official extension entries reject with their ordinals
    assertVerdict mintPlan closedAccept? (extensionMint 1 (gateU16 1 ++ gateU16 56))
      (.reject (.unsupported 1)) &&
    assertVerdict mintPlan closedAccept? (extensionMint 1 (gateU16 14 ++ gateU16 65))
      (.reject (.unsupported 14)) &&
    -- unknown ordinal outside the official set
    assertVerdict accountPlan closedAccept?
      (extensionAccount (gateU16 0x9999 ++ gateU16 4)) (.reject (.unknown 0x9999)) &&
    -- a well-formed body does not change the closed verdict
    assertVerdict accountPlan closedAccept?
      (extensionAccount (gateU16 0x9999 ++ gateU16 2 ++ #[1, 2]))
      (.reject (.unknown 0x9999))) = true

-- With a synthetic classifier over official ordinals, the full cursor performs bounded body
-- advances using only its scalar count and UInt64 duplicate bitmap: multiple headers, OOB bodies,
-- duplicates, and the compile-time header-count bound. The straight-line mirror is intentionally
-- not consulted here: it only models the closed classifier.
#guard
  (let synthetic : UInt64 → Bool := fun t => 1 ≤ t && t ≤ UInt64.ofNat knownExtensionMax
   let entry (t : UInt64) (len : Nat) : Array UInt8 :=
     gateU16 t.toNat ++ gateU16 len ++ (Array.range len |>.map (fun _ => (1 : UInt8)))
   -- one then several valid bounded headers advance and accept
   evaluate accountPlan synthetic (view := gateView (extensionAccount (entry 1 2))) == .accept &&
   evaluate accountPlan synthetic
     (view := gateView (extensionAccount
       (entry 1 2 ++ entry 2 4 ++ entry 3 8))) == .accept &&
   -- body out of bounds
   evaluate accountPlan synthetic
     (view := gateView (extensionAccount (gateU16 1 ++ gateU16 9 ++ #[1, 2]))) ==
       .reject .bodyOutOfBounds &&
   -- distinct accepted entries advance; a repeated one is a duplicate
   evaluate accountPlan synthetic
     (view := gateView (extensionAccount (entry 1 2 ++ entry 2 0))) == .accept &&
   evaluate accountPlan synthetic
     (view := gateView (extensionAccount (entry 1 2 ++ entry 1 2))) == .reject (.duplicate 1) &&
   -- a smaller compile-time plan bound rejects the third distinct entry
   evaluate { accountPlan with maxHeaders := 2 } synthetic
     (view := gateView (extensionAccount (entry 1 0 ++ entry 2 0 ++ entry 3 0))) ==
       .reject .headerCount &&
   -- all 28 distinct official ordinals fit the fixed bitmap and default bound
   evaluate accountPlan synthetic
     (view := gateView (extensionAccount
       (Array.range defaultMaxHeaders |>.flatMap
         (fun i => entry (UInt64.ofNat (i + 1)) 0)))) == .accept) = true

-- Wrap-checked cursor arithmetic rejects u64 wraparound instead of wrapping past `data_len`;
-- the interpreter's subtraction-form body bound keeps the advance inside `data_len` even at the
-- u64 edge, so the defensive wrap checks only fire on inconsistent states.
#guard
  (let synthetic : UInt64 → Bool := fun _ => true
   let far : UInt64 := 18446744073709551611  -- 2^64 - 5
   let huge : UInt64 := 18446744073709551615
   addBounded 18446744073709551615 1 == none &&
     addBounded far 4 == some 18446744073709551615 &&
     run accountPlan synthetic (fun _ => none)
       { dataLen := huge, readByte := fun _ => some 0 } (defaultMaxHeaders + 1)
       { cursor := far, count := 0, seenMask := 0 } == .accept) = true

#guard match planFor (.token2022Base .mint) with
  | .ok plan => plan == mintPlan
  | .error _ => false

#guard match planFor (.token2022Base .account) with
  | .ok plan => plan == accountPlan
  | .error _ => false

end TokenTlvGates

end Tests.Token2022Spec
