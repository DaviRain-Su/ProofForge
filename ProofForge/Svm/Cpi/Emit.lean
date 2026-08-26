namespace ProofForge.Svm.Cpi.Emit

/-- Dynamic CPI descriptors share the established 1,024-byte stack bank rooted at `r10-2048`.
The payload itself may live in bounded heap storage and is therefore not counted in this frame. -/
def maxScratchBytes : Nat := 1024

structure Context where
  headerStack : Nat → Nat
  accountCount : Nat

private def emitFillAccountInfoFromHeader (tag : String) (srcStack : Nat) : String :=
  let aligned := "dynamic_cpi_fill_" ++ tag ++ "_" ++ toString srcStack
  s!"\
  ldxdw r8, [r10 - {srcStack}]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + 0], r1
  mov64 r1, r8
  add64 r1, 72
  stxdw [r5 + 8], r1
  ldxdw r1, [r8 + 80]
  stxdw [r5 + 16], r1
  mov64 r1, r8
  add64 r1, 88
  stxdw [r5 + 24], r1
  mov64 r1, r8
  add64 r1, 40
  stxdw [r5 + 32], r1
  mov64 r1, r8
  add64 r1, 88
  ldxdw r4, [r8 + 80]
  add64 r1, r4
  add64 r1, MAX_PERMITTED_DATA_INCREASE
  mov64 r2, r4
  and64 r2, 7
  jeq r2, 0, {aligned}
  lddw r3, 8
  sub64 r3, r2
  add64 r1, r3
{aligned}:
  ldxdw r1, [r1 + 0]
  stxdw [r5 + 40], r1
  ldxb r1, [r8 + 1]
  stxb [r5 + 48], r1
  ldxb r1, [r8 + 2]
  stxb [r5 + 49], r1
  ldxb r1, [r8 + 3]
  stxb [r5 + 50], r1
  lddw r1, 0
  stxb [r5 + 51], r1
  stxb [r5 + 52], r1
  stxb [r5 + 53], r1
  stxb [r5 + 54], r1
  stxb [r5 + 55], r1
"

/-- Emit one readonly signer meta and one signer-seed group, then invoke the current program with
data pointer/length loaded from component-owned stack cells. This sink is independent of any event
schema and can be reused by bounded codecs that retain payload bytes outside the CPI stack bank. -/
def emitDynamicSignedSelf (context : Context) (label : String)
    (logAccount : Nat) (authoritySeed : String)
    (dataPointerStack dataLengthStack bumpStack : Nat) : Except String String := do
  let n := context.accountCount
  let metaOff := 0
  let instructionOff := 16
  let infoOff := instructionOff + 40
  let seedOff := infoOff + 56 * n
  let bumpByte := ((seedOff + authoritySeed.length + 7) / 8) * 8
  let seedEntries := bumpByte + 8
  let bumpEntry := seedEntries + 16
  let signerGroup := bumpEntry + 16
  let frameEnd := signerGroup + 16
  if frameEnd > maxScratchBytes then
    throw s!"extract/unsupported: dynamic signed CPI scratch requires {frameEnd} bytes, maximum is {maxScratchBytes}"
  let physicalLogAccount := logAccount + 1
  let mut seedBytes := ""
  for i in [0:authoritySeed.length] do
    let character := authoritySeed.toList[i]!
    seedBytes := seedBytes ++
      s!"  lddw r1, {character.toNat}\n  stxb [r9 + {seedOff + i}], r1\n"
  let mut infos := ""
  for i in [0:n] do
    infos := infos ++ emitFillAccountInfoFromHeader label (context.headerStack i)
    if i + 1 < n then
      infos := infos ++ "  add64 r5, 56\n"
  return s!"\
  ; dynamic signed self CPI account={physicalLogAccount} data<=1246
  mov64 r9, r10
  add64 r9, -2048
  mov64 r5, r9
  add64 r5, {metaOff}
  ldxdw r8, [r10 - {context.headerStack physicalLogAccount}]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + 0], r1
  lddw r1, 0
  stxb [r5 + 8], r1
  lddw r1, 1
  stxb [r5 + 9], r1
  lddw r1, 0
  stxb [r5 + 10], r1
  stxb [r5 + 11], r1
  stxb [r5 + 12], r1
  stxb [r5 + 13], r1
  stxb [r5 + 14], r1
  stxb [r5 + 15], r1
  mov64 r8, r9
  add64 r8, {instructionOff}
  ldxdw r1, [r10 - {context.headerStack n}]
  ldxdw r2, [r1 + 0]
  add64 r1, 8
  add64 r1, r2
  stxdw [r8 + 0], r1
  mov64 r1, r9
  add64 r1, {metaOff}
  stxdw [r8 + 8], r1
  lddw r1, 1
  stxdw [r8 + 16], r1
  ldxdw r1, [r10 - {dataPointerStack}]
  stxdw [r8 + 24], r1
  ldxdw r1, [r10 - {dataLengthStack}]
  stxdw [r8 + 32], r1
  stxdw [r10 - 112], r8
  mov64 r5, r9
  add64 r5, {infoOff}
{infos}{seedBytes}\
  mov64 r1, r9
  add64 r1, {seedOff}
  stxdw [r9 + {seedEntries}], r1
  lddw r1, {authoritySeed.length}
  stxdw [r9 + {seedEntries + 8}], r1
  ldxdw r1, [r10 - {bumpStack}]
  stxb [r9 + {bumpByte}], r1
  mov64 r1, r9
  add64 r1, {bumpByte}
  stxdw [r9 + {bumpEntry}], r1
  lddw r1, 1
  stxdw [r9 + {bumpEntry + 8}], r1
  mov64 r1, r9
  add64 r1, {seedEntries}
  stxdw [r9 + {signerGroup}], r1
  lddw r1, 2
  stxdw [r9 + {signerGroup + 8}], r1
  ldxdw r1, [r10 - 112]
  mov64 r2, r9
  add64 r2, {infoOff}
  lddw r3, {n}
  mov64 r4, r9
  add64 r4, {signerGroup}
  lddw r5, 1
  call sol_invoke_signed_c
  jeq r0, 0, dynamic_cpi_ok_{label}
  exit
dynamic_cpi_ok_{label}:
"

end ProofForge.Svm.Cpi.Emit
