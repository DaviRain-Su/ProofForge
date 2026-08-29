import ProofForge.Svm.Ops
import ProofForge.Svm.Lamports

namespace ProofForge.Svm.Lamports.Emit

/-- The lamport backend shares value loading, current-program owner comparison, and the walked
canonical-header frame with the other account components. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat

/-- Checked physical lamport transfer between two statically addressed walked headers. Every
condition is preflighted before either store, in this order: canonical header pointers differ
(duplicate aliases fail closed), both accounts are writable, the source owner is the current
program id, the source balance covers `amount`, and the destination addition cannot overflow.
Any failure exits `Custom(1)` without writes. Amount zero passes the same validation and stores
two no-op writes; the signed total delta is always zero. The destination may be foreign-owned and
no executable check is imposed. -/
def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .transfer source destination amount => do
      let loadAmount ← context.loadValue amount 8 0 s!"{label}_amount"
      let ownerCheck := context.loadOwnerIsSelf source 16 s!"{label}_owner"
      let distinct := s!"lt_distinct_{label}"
      let funded := s!"lt_funded_{label}"
      let store := s!"lt_store_{label}"
      let fail := s!"lt_fail_{label}"
      let done := s!"lt_done_{label}"
      return loadAmount ++ ownerCheck ++ s!"\
  ; checked lamport transfer acc{source} -> acc{destination}
  ldxdw r8, [r10 - {context.headerStack source}]
  ldxdw r9, [r10 - {context.headerStack destination}]
  jne r8, r9, {distinct}
  ja {fail}
{distinct}:
  ldxb r1, [r8 + 2]
  jeq r1, 0, {fail}
  ldxb r1, [r9 + 2]
  jeq r1, 0, {fail}
  ldxdw r1, [r10 - 16]
  jne r1, 0, {fail}
  ldxdw r2, [r10 - 8]
  ldxdw r1, [r8 + 72]
  jge r1, r2, {funded}
  ja {fail}
{funded}:
  ldxdw r3, [r9 + 72]
  lddw r4, 0xffffffffffffffff
  sub64 r4, r2
  jge r4, r3, {store}
  ja {fail}
{store}:
  sub64 r1, r2
  stxdw [r8 + 72], r1
  add64 r3, r2
  stxdw [r9 + 72], r3
  ja {done}
{fail}:
  lddw r0, 0x1
  exit
{done}:
"

end ProofForge.Svm.Lamports.Emit
