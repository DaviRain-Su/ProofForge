import ProofForge.Svm.AccountData
import ProofForge.Svm.Ops

namespace ProofForge.Svm.AccountData.Emit

/-- Account resize shares value loading, program-owner comparison, and canonical walked headers
with the other direct-account components. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat
  originalDataLenStack : Nat → Nat

private def failure : String :=
  "  lddw r0, 0x1\n  exit\n"

/--
Emit the current zero-initializing Solana `AccountInfo::resize` contract over one fixed external
account header. Every fallible condition is checked before changing the current length or payload:

1. the selected external account must not alias managed state account zero;
2. it must be writable and owned by the executing program;
3. current and requested lengths must not exceed the 10 MiB account ceiling;
4. both current and requested growth above the immutable invocation-entry length captured by the
   account walk must be at most 10,240 bytes.

Shrinking changes only the current length. Growing zeroes `[current,new)` with `sol_memset_` before
publishing the new length, so shrink-then-grow in one invocation cannot reveal stale bytes. Equal
length is a validated no-op. Canonical aliases among external positions share the same header and
therefore the same resize; no pointer enters source, IR values, account state, or return data.
-/
def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .resize account newLength => do
      let loadLength ← context.loadValue newLength 8 0 s!"{label}_new_length"
      let ownerCheck := context.loadOwnerIsSelf account 16 s!"{label}_owner"
      let distinct := s!"account_resize_external_{label}"
      let writable := s!"account_resize_writable_{label}"
      let owned := s!"account_resize_owned_{label}"
      let currentBound := s!"account_resize_current_bound_{label}"
      let requestedBound := s!"account_resize_requested_bound_{label}"
      let grow := s!"account_resize_grow_{label}"
      let store := s!"account_resize_store_{label}"
      let done := s!"account_resize_done_{label}"
      let fail := s!"account_resize_fail_{label}"
      return loadLength ++ ownerCheck ++ s!"\
  ; checked zero-initializing account-data resize acc{account}
  ldxdw r8, [r10 - {context.headerStack account}]
  ldxdw r9, [r10 - {context.headerStack 0}]
  jne r8, r9, {distinct}
  ja {fail}
{distinct}:
  ldxb r1, [r8 + 2]
  jne r1, 0, {writable}
  ja {fail}
{writable}:
  ldxdw r1, [r10 - 16]
  jeq r1, 0, {owned}
  ja {fail}
{owned}:
  ldxdw r1, [r10 - 8]
  lddw r2, {Memory.maxAccountDataBytes}
  jgt r1, r2, {fail}
  ldxdw r4, [r8 + 80]
  jgt r4, r2, {fail}
  ldxdw r3, [r10 - {context.originalDataLenStack account}]
  jgt r4, r3, account_resize_check_current_growth_{label}
  ja {currentBound}
account_resize_check_current_growth_{label}:
  mov64 r5, r4
  sub64 r5, r3
  jgt r5, {AccountData.maxPermittedDataIncrease}, {fail}
{currentBound}:
  jgt r1, r3, account_resize_check_requested_growth_{label}
  ja {requestedBound}
account_resize_check_requested_growth_{label}:
  mov64 r5, r1
  sub64 r5, r3
  jgt r5, {AccountData.maxPermittedDataIncrease}, {fail}
{requestedBound}:
  jeq r1, r4, {done}
  jgt r1, r4, {grow}
  ja {store}
{grow}:
  mov64 r3, r1
  sub64 r3, r4
  mov64 r1, r8
  add64 r1, 88
  add64 r1, r4
  lddw r2, 0
  call sol_memset_
  ldxdw r8, [r10 - {context.headerStack account}]
{store}:
  ldxdw r1, [r10 - 8]
  stxdw [r8 + 80], r1
  ja {done}
{fail}:
{failure}{done}:
"

end ProofForge.Svm.AccountData.Emit
