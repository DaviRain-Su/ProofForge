import ProofForge.Svm.Cpi.TokenTlv

/-!
# Emitter for the bounded Token-2022 TLV account-data policy

Lowers `TokenTlv.Plan` to the sBPF preflight that runs before the Token-2022 `TransferChecked`
CPI. The machine is the straight-line specialization of `TokenTlv.evaluate` for the closed
classifier (`evaluate_closed_eq_straightline`): only the classic base layout or an extension-form
account whose TLV region starts with an official end/padding form proceeds; every other form exits
`Custom(1)` atomically before any persistent write or CPI. Scalar registers only: no heap object,
no pointer beyond the live account header, no runtime-selected geometry.
-/

namespace ProofForge.Svm.Cpi.TokenTlv.Emit

structure Context where
  headerStack : Nat → Nat

/-- Account header layout: data length at +80, data bytes at +88. -/
def dataLenOffset : Nat := 80

def dataPtrOffset : Nat := 88

/--
Emit the TLV policy preflight for the account at physical index `physical`. All rejection paths
jump to the shared `cpi_data_len_err_{label}` exit; the accept path falls through to
`cpi_data_len_ok_{label}`, which the ordinary data-length policy also uses.
-/
def emitPreflight (ctx : Context) (label : String) (physical : Nat) (plan : Plan) :
    Except String String := do
  unless plan.wellFormed do
    throw "extract/unsupported: malformed Token-2022 TLV account-data plan"
  let err := s!"cpi_data_len_err_{label}"
  -- The short-remainder probe target is unique per account: two constrained accounts in one
  -- invocation must not share a label.
  let okFull := s!"cpi_data_len_ok_{label}_p{physical}_full"
  -- Accepting this account continues into the next account's policy; only the final
  -- fall-through reaches the shared `ok` exit, so no account's checks can be skipped.
  let next := s!"cpi_data_len_next_{label}_p{physical}"
  let src := ctx.headerStack physical

  let padding :=
    (List.range plan.paddingBytes).foldl (init := "") fun out i =>
      out ++ s!"  ldxb r4, [r3 + {plan.baseLen + i}]\n  jne r4, 0, {err}\n"
  return s!"\
  ; token-2022 TLV account-data policy ({repr plan.kind}) for physical account {physical}
  ldxdw r1, [r10 - {src}]
  ldxdw r2, [r1 + {dataLenOffset}]
  ; the account data bytes follow the fixed 88-byte header inline, so the data pointer is
  ; computed, never loaded (there is no pointer field in the serialized input)
  mov64 r3, r1
  add64 r3, {dataPtrOffset}
  ; official Multisig::LEN is never an extension-bearing mint/account
  jeq r2, {multisigLen}, {err}
  ; base state span
  jlt r2, {plan.baseLen}, {err}
  jeq r2, {plan.baseLen}, {next}
  ; extension form carries the full base+padding+type-byte span
  jlt r2, {tlvStart}, {err}
{padding}  ; AccountType byte must match the constrained base state
  ldxb r4, [r3 + {typeByteOffset}]
  jne r4, {plan.typeByte}, {err}
  ; forward-only bounded TLV cursor, first entry: every non-end entry rejects
  mov64 r4, r2
  sub64 r4, {tlvStart}
  jeq r4, 0, {next}
  jeq r4, 1, {next}
  ; rem \u2265 2 proves both type bytes are inside data_len; rem \u2265 4 proves the full header
  ldxb r5, [r3 + {tlvStart}]
  jne r5, 0, {err}
  ldxb r5, [r3 + {tlvStart + 1}]
  jgt r4, 3, {okFull}
  ; two or three trailing bytes: only the Uninitialized(0) type is official
  jne r5, 0, {err}
  ja {next}
{okFull}:
  ; Uninitialized(0) ends the region; everything after is ignored, as on-chain
  jne r5, 0, {err}
  ja {next}
{next}:
"

end ProofForge.Svm.Cpi.TokenTlv.Emit
