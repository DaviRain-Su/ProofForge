import ProofForge.Svm.IR

namespace ProofForge.Svm.AccountView.Emit

/-- The view backend receives the surrounding method's value loader and walked-header frame.
It never owns scratch: selection keeps state in registers only. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  headerStack : Nat → Nat
  accountCount : Nat

/-- Walk from the first transaction account header to `base + index`, checking every account tag
and advancing through the real account geometry. This is the dynamic twin of the static
`emitWalkAccounts` prelude walk: same 88-byte header layout, same data-length/alignment skip, no
copies and no pointers outside the invocation. -/
private def emitSelect (context : Context) (view : View) (index : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadIndex ← context.loadValue index (stackOff + 8) (nonce + 1) (scope ++ "_index")
  let token := IR.u64Hex (Core.IR.fnv1a64
    s!"{scope}:{stackOff}:{nonce}:{view.base}:{view.capacity}")
  let fail := s!"fail_view_index_{token}"
  let selected := s!"ok_view_select_{token}"
  let ok := s!"ok_view_{token}"
  let loop := s!"view_walk_{token}"
  let align := s!"view_al_{token}"
  return loadIndex ++
    s!"\
  ; select bounded remaining account base={view.base} capacity={view.capacity}
  ldxdw r2, [r10 - {stackOff + 8}]
  lddw r3, {view.capacity}
  jge r2, r3, {fail}
  mov64 r9, r2
  lddw r2, {view.base}
  add64 r9, r2
  ldxdw r2, [r6 + NUM_ACCOUNTS]
  jge r9, r2, {fail}
  mov64 r8, r6
  add64 r8, 8
{loop}:
  ldxb r1, [r8 + 0]
  jne r1, 0xff, {fail}
  jeq r9, 0, {selected}
  ldxdw r4, [r8 + 80]
  mov64 r5, r8
  add64 r5, 88
  add64 r5, r4
  add64 r5, MAX_PERMITTED_DATA_INCREASE
  mov64 r1, r4
  and64 r1, 7
  jeq r1, 0, {align}
  lddw r3, 8
  sub64 r3, r1
  add64 r5, r3
{align}:
  ldxdw r1, [r5 + 0]
  add64 r5, 8
  mov64 r8, r5
  sub64 r9, 1
  ja {loop}
{selected}:
  ldxb r1, [r8 + 0]
  jne r1, 0xff, {fail}
  ja {ok}
{fail}:
  lddw r0, 0x1
  exit
{ok}:
"

/-- Load one header field from the selected account. -/
private def emitHeader (field : Header) (stackOff : Nat) : String :=
  let comment := s!"; load view header {Header.canonical field}"
  match field with
  | .lamports =>
      s!"{comment}\n  ldxdw r1, [r8 + 72]\n  stxdw [r10 - {stackOff}], r1\n"
  | .dataLen =>
      s!"{comment}\n  ldxdw r1, [r8 + 80]\n  stxdw [r10 - {stackOff}], r1\n"
  | .isSigner =>
      s!"{comment}\n  ldxb r1, [r8 + 1]\n  stxdw [r10 - {stackOff}], r1\n"
  | .isWritable =>
      s!"{comment}\n  ldxb r1, [r8 + 2]\n  stxdw [r10 - {stackOff}], r1\n"
  | .key word =>
      let off := 8 + 8 * word
      s!"{comment}\n  ldxdw r1, [r8 + {off}]\n  stxdw [r10 - {stackOff}], r1\n"

/-- Compare the selected account's 32-byte owner with the current program id. Equal writes 0,
otherwise 1. Every account-view query forces the walked ABI, so the trailing header-stack cell
always points to the real instruction data after the runtime account walk. -/
private def emitOwnerIsSelf (context : Context) (scope : String) (stackOff : Nat) : String :=
  let progId := s!"\
  ldxdw r3, [r10 - {context.headerStack context.accountCount}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
"
  let owner := s!"\
  mov64 r2, r8
  add64 r2, 40
"
  s!"\
  ; view ownerIsSelf
{progId}{owner}  ldxdw r1, [r2 + 0]
  ldxdw r4, [r3 + 0]
  jne r1, r4, ois_no_view_{scope}_{stackOff}
  ldxdw r1, [r2 + 8]
  ldxdw r4, [r3 + 8]
  jne r1, r4, ois_no_view_{scope}_{stackOff}
  ldxdw r1, [r2 + 16]
  ldxdw r4, [r3 + 16]
  jne r1, r4, ois_no_view_{scope}_{stackOff}
  ldxdw r1, [r2 + 24]
  ldxdw r4, [r3 + 24]
  jne r1, r4, ois_no_view_{scope}_{stackOff}
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
  ja ois_done_view_{scope}_{stackOff}
ois_no_view_{scope}_{stackOff}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
ois_done_view_{scope}_{stackOff}:
"

/-- Load one u64 from the selected account's data. `data_len` is re-checked before the data
pointer is formed so a short account exits `Custom(1)` instead of reading past its bytes. -/
private def emitDataWord (word : Nat) (scope : String) (stackOff nonce : Nat) : String :=
  let required := 8 * word + 8
  let ok := s!"ok_view_data_{scope}_{nonce}_{stackOff}"
  s!"\
  ; load view data word {word}
  ldxdw r4, [r8 + 80]
  lddw r3, {required}
  jge r4, r3, {ok}
  lddw r0, 0x1
  exit
{ok}:
  ldxdw r1, [r8 + {88 + 8 * word}]
  stxdw [r10 - {stackOff}], r1
"

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .header view field, #[index] => do
      let select ← emitSelect context view index stackOff nonce scope
      return select ++ emitHeader field stackOff
  | .ownerIsSelf view, #[index] => do
      let select ← emitSelect context view index stackOff nonce scope
      return select ++ emitOwnerIsSelf context scope stackOff
  | .dataWord view word, #[index] => do
      let select ← emitSelect context view index stackOff nonce scope
      return select ++ emitDataWord word scope stackOff nonce
  | _, _ => .error "extract/ir: malformed account-view query operands"

end ProofForge.Svm.AccountView.Emit
