/-!
## E-infinity knife 66 - Loader account-9 header/key after skip chain (`svm-sem-071`)

Knife 65 proves the nonuple skip lands on the account-9 dup marker. Emit then treats that
address as the account-9 header cursor (marker byte, key at `+8`). This knife composes the
account-0/1/2/3/4/5/6/7/8 skip chain with an account-9 meta load and proves agreement with absolute
`r6`-relative loads. Still not account-9 flags/budget/owner, full vectors, syscalls, CPI,
or ELF accept.
-/

/-- Absolute offset/VA of account-9 first key limb. -/
def account9KeyOffset : Nat := account9HeaderOffset + 8
def account9KeyAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9KeyOffset

/-- Seed nonuple-skip layout plus account-9 first key limb. -/
def account9MetaInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64) : Option Mem := do
  let m ← account8SkipNextInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker
  storev .m64 m account9KeyAddr (.vlong key9Word)

/-- Typed nonuple skip then account-9 meta: `ldxb r1,[r2+0]`; `ldxdw r2,[r2+8]`; stage key. -/

def walkAccount9MetaAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let keyOff ← positiveOffset? 8
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 zeroOff,
    .ldx .m64 .br4 .br2 keyOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br2) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9MetaAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9MetaAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 dup marker and first key limb. -/
def evalAbsAccount9Meta? (memory : Mem) : Option (U8 × U64) := do
  let dup ← loadv .m8 memory account9HeaderAddr
  let key ← loadv .m64 memory account9KeyAddr
  match dup, key with
  | .vbyte d, .vlong k => some (d, k)
  | _, _ => none

theorem walkAccount9MetaAfterSkipChain_verified :
    (walkAccount9MetaAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+meta: marker=`0xff`, key=`0x79`, key staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_key_0x79 :
    (do
      let mem ← account9MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79
      let (regs, finalMem) ← evalWalkAccount9MetaAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == account0NonDupMarker.setWidth 64 &&
        regs .br2 == 0x79 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x79))) =
      some true := by
  native_decide

/-- Walked account-9 meta after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9MetaAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9MetaInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79
      let (regs, _) ← evalWalkAccount9MetaAfterSkipChainToStack? rhsStackOffset mem
      let (dup, key) ← evalAbsAccount9Meta? mem
      pure (regs .br1 == dup.setWidth 64 && regs .br2 == key &&
        dup == 0xB6 && key == 0x79)) =
      some true := by
  native_decide

/-!
## E-infinity knife 67 - Loader account-9 signer/writable after skip chain (`svm-sem-072`)

Knife 66 lands the cursor on account-9 meta. Emit then gates with `ldxb` of header+1 (signer)
and +2 (writable). This knife composes the nonuple skip chain with those flag loads and proves
agreement with absolute `r6`-relative loads. Still not budget/owner/exec-rent for account-9,
full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute VAs for account-9 signer and writable flag bytes. -/
def account9SignerAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account9HeaderOffset + 1)
def account9WritableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 (account9HeaderOffset + 2)

/-- Seed nonuple-skip+account-9 meta layout plus signer/writable flags. -/
def account9FlagsInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8) : Option Mem := do
  let m₁ ← account9MetaInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word
  let m₂ ← storev .m8 m₁ account9SignerAddr (.vbyte acc9Signer)
  storev .m8 m₂ account9WritableAddr (.vbyte acc9Writable)

/-- Typed nonuple skip then account-9 flags: `ldxb r1,[r2+1]`; `ldxb r2,[r2+2]`; stage signer. -/

def walkAccount9FlagsAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let signerOff ← positiveOffset? 1
  let writableOff ← positiveOffset? 2
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 signerOff,
    .ldx .m8 .br4 .br2 writableOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9FlagsAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9FlagsAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 signer and writable flag bytes. -/
def evalAbsAccount9Flags? (memory : Mem) : Option (U8 × U8) := do
  let signer ← loadv .m8 memory account9SignerAddr
  let writable ← loadv .m8 memory account9WritableAddr
  match signer, writable with
  | .vbyte s, .vbyte w => some (s, w)
  | _, _ => none

theorem walkAccount9FlagsAfterSkipChain_verified :
    (walkAccount9FlagsAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+flags: signer=`1`, writable=`1`, signer staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_signer_writable_1 :
    (do
      let mem ← account9FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1
      let (regs, finalMem) ← evalWalkAccount9FlagsAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 1 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-9 flags after skip chain agree with absolute `r6`-relative loads. -/
theorem walkAccount9FlagsAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9FlagsInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0
      let (regs, _) ← evalWalkAccount9FlagsAfterSkipChainToStack? rhsStackOffset mem
      let (signer, writable) ← evalAbsAccount9Flags? mem
      pure (regs .br1 == signer.setWidth 64 && regs .br2 == writable.setWidth 64 &&
        signer == 1 && writable == 0)) =
      some true := by
  native_decide

/-!
## E-infinity knife 68 - Loader account-9 lamports/data_len after skip chain (`svm-sem-073`)

Knife 67 covers account-9 signer/writable after the skip chain. Emit then reads account-9
lamports and data_len (`+0x48` / `+0x50`). This knife composes the nonuple skip chain with
those word loads and proves agreement with absolute `r6`-relative loads. Still not owner/executable/rent
for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 lamports and data_len. -/
def account9LamportsOffset : Nat :=
  account9HeaderOffset + (account0LamportsOffset - account0HeaderOffset)
def account9DataLenOffset : Nat :=
  account9HeaderOffset + (account0DataLenOffset - account0HeaderOffset)
def account9LamportsAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9LamportsOffset
def account9DataLenAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9DataLenOffset

/-- Seed nonuple-skip+account-9 flags layout plus lamports and data_len words. -/
def account9BudgetInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64) : Option Mem := do
  let m₁ ← account9FlagsInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
  let m₂ ← storev .m64 m₁ account9LamportsAddr (.vlong acc9Lamports)
  storev .m64 m₂ account9DataLenAddr (.vlong acc9DataLen)

/-- Typed nonuple skip then account-9 budget: `ldxdw r1,[r2+0x48]`; `ldxdw r2,[r2+0x50]`. -/

def walkAccount9BudgetAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let lamportsOff ← positiveOffset? (account0LamportsOffset - account0HeaderOffset)
  let dataLenFieldOff ← positiveOffset? (account0DataLenOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 lamportsOff,
    .ldx .m64 .br4 .br2 dataLenFieldOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9BudgetAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9BudgetAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 lamports and data_len. -/
def evalAbsAccount9Budget? (memory : Mem) : Option (U64 × U64) := do
  let lamports ← loadv .m64 memory account9LamportsAddr
  let dataLen ← loadv .m64 memory account9DataLenAddr
  match lamports, dataLen with
  | .vlong l, .vlong d => some (l, d)
  | _, _ => none

theorem walkAccount9BudgetAfterSkipChain_verified :
    (walkAccount9BudgetAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+budget: lamports=`9000`, data_len=`192`, lamports staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_lamports_9000_dataLen_192 :
    (do
      let mem ← account9BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192
      let (regs, finalMem) ← evalWalkAccount9BudgetAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 9000 && regs .br2 == 192 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 9000))) =
      some true := by
  native_decide

/-- Walked account-9 budget after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9BudgetAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9BudgetInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192
      let (regs, _) ← evalWalkAccount9BudgetAfterSkipChainToStack? rhsStackOffset mem
      let (lamports, dataLen) ← evalAbsAccount9Budget? mem
      pure (regs .br1 == lamports && regs .br2 == dataLen &&
        lamports == 9000 && dataLen == 192)) =
      some true := by
  native_decide

/-!
## E-infinity knife 69 - Loader account-9 owner limbs 0/1 after skip chain (`svm-sem-074`)

Knife 68 completes account-9 lamports/data_len after the skip chain. Emit then reads account-9
owner pubkey limbs 0 and 1 (`+0x28` / `+0x30`). This knife composes the nonuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not owner
limbs 2/3 or exec/rent for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 owner limbs 0 and 1. -/
def account9Owner0Offset : Nat :=
  account9HeaderOffset + (account0Owner0Offset - account0HeaderOffset)
def account9Owner1Offset : Nat :=
  account9HeaderOffset + (account0Owner1Offset - account0HeaderOffset)
def account9Owner0Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner0Offset
def account9Owner1Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner1Offset

/-- Seed nonuple-skip+account-9 budget layout plus owner limbs 0/1. -/
def account9OwnerInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64) : Option Mem := do
  let m₁ ← account9BudgetInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen
  let m₂ ← storev .m64 m₁ account9Owner0Addr (.vlong acc9Owner0)
  storev .m64 m₂ account9Owner1Addr (.vlong acc9Owner1)

/-- Typed nonuple skip then account-9 owner lo: `ldxdw r1,[r2+0x28]`; `ldxdw r2,[r2+0x30]`. -/

def walkAccount9OwnerAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner0Off ← positiveOffset? (account0Owner0Offset - account0HeaderOffset)
  let owner1Off ← positiveOffset? (account0Owner1Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner0Off,
    .ldx .m64 .br4 .br2 owner1Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9OwnerAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9OwnerAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 owner limbs 0 and 1. -/
def evalAbsAccount9Owner? (memory : Mem) : Option (U64 × U64) := do
  let owner0 ← loadv .m64 memory account9Owner0Addr
  let owner1 ← loadv .m64 memory account9Owner1Addr
  match owner0, owner1 with
  | .vlong o0, .vlong o1 => some (o0, o1)
  | _, _ => none

theorem walkAccount9OwnerAfterSkipChain_verified :
    (walkAccount9OwnerAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+owner lo: owner0=`0xEC`, owner1=`0xFD`, owner0 staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_owner0_0xEC_owner1_0xFD :
    (do
      let mem ← account9OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD
      let (regs, finalMem) ← evalWalkAccount9OwnerAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0xEC && regs .br2 == 0xFD &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0xEC))) =
      some true := by
  native_decide

/-- Walked account-9 owner lo after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9OwnerAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9OwnerInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD
      let (regs, _) ← evalWalkAccount9OwnerAfterSkipChainToStack? rhsStackOffset mem
      let (owner0, owner1) ← evalAbsAccount9Owner? mem
      pure (regs .br1 == owner0 && regs .br2 == owner1 &&
        owner0 == 0xEC && owner1 == 0xFD)) =
      some true := by
  native_decide

/-!
## E-infinity knife 70 - Loader account-9 owner limbs 2/3 after skip chain (`svm-sem-075`)

Knife 69 completes account-9 owner limbs 0/1 after the skip chain. Emit then reads account-9
owner pubkey limbs 2 and 3 (`+0x38` / `+0x40`). This knife composes the nonuple skip chain
with those word loads and proves agreement with absolute `r6`-relative loads. Still not
exec/rent for account-9, full vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 owner limbs 2 and 3. -/
def account9Owner2Offset : Nat :=
  account9HeaderOffset + (account0Owner2Offset - account0HeaderOffset)
def account9Owner3Offset : Nat :=
  account9HeaderOffset + (account0Owner3Offset - account0HeaderOffset)
def account9Owner2Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner2Offset
def account9Owner3Addr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9Owner3Offset

/-- Seed nonuple-skip+account-9 owner layout plus owner limbs 2/3. -/
def account9OwnerHiInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64)
    (acc9Owner2 acc9Owner3 : U64) : Option Mem := do
  let m₁ ← account9OwnerInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1
  let m₂ ← storev .m64 m₁ account9Owner2Addr (.vlong acc9Owner2)
  storev .m64 m₂ account9Owner3Addr (.vlong acc9Owner3)

/-- Typed nonuple skip then account-9 owner hi: `ldxdw r1,[r2+0x38]`; `ldxdw r2,[r2+0x40]`. -/

def walkAccount9OwnerHiAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let owner2Off ← positiveOffset? (account0Owner2Offset - account0HeaderOffset)
  let owner3Off ← positiveOffset? (account0Owner3Offset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 owner2Off,
    .ldx .m64 .br4 .br2 owner3Off,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9OwnerHiAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9OwnerHiAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 owner limbs 2 and 3. -/
def evalAbsAccount9OwnerHi? (memory : Mem) : Option (U64 × U64) := do
  let owner2 ← loadv .m64 memory account9Owner2Addr
  let owner3 ← loadv .m64 memory account9Owner3Addr
  match owner2, owner3 with
  | .vlong o2, .vlong o3 => some (o2, o3)
  | _, _ => none

theorem walkAccount9OwnerHiAfterSkipChain_verified :
    (walkAccount9OwnerHiAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+owner hi: owner2=`0x1E`, owner3=`0x2F`, owner2 staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_owner2_0x1E_owner3_0x2F :
    (do
      let mem ← account9OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F
      let (regs, finalMem) ← evalWalkAccount9OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 0x1E && regs .br2 == 0x2F &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 0x1E))) =
      some true := by
  native_decide

/-- Walked account-9 owner hi after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9OwnerHiAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9OwnerHiInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F
      let (regs, _) ← evalWalkAccount9OwnerHiAfterSkipChainToStack? rhsStackOffset mem
      let (owner2, owner3) ← evalAbsAccount9OwnerHi? mem
      pure (regs .br1 == owner2 && regs .br2 == owner3 &&
        owner2 == 0x1E && owner3 == 0x2F)) =
      some true := by
  native_decide

/-!
## E-infinity knife 71 - Loader account-9 executable + rent_epoch after skip chain (`svm-sem-076`)

Knife 70 completes account-9 owner pubkey after the skip chain. Emit then reads account-9
executable (`header+3`) and rent_epoch (`header+0x2858` for the zero-data layout). This knife
composes the nonuple skip chain with those loads and proves agreement with absolute
`r6`-relative loads. Still not full multi-account vectors, syscalls, CPI, or ELF accept.
-/

/-- Absolute offsets/VAs for account-9 executable and zero-dataLen rent_epoch. -/
def account9ExecutableOffset : Nat := account9HeaderOffset + 3
def account9RentEpochOffset : Nat :=
  account9HeaderOffset + (account0RentEpochOffset - account0HeaderOffset)
def account9ExecutableAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9ExecutableOffset
def account9RentEpochAddr : U64 :=
  mmInputStart + BitVec.ofNat 64 account9RentEpochOffset

/-- Seed nonuple-skip+account-9 owner layout plus executable flag and rent_epoch. -/
def account9ExecRentInputMem (value arg0 key0Limb : U64) (acc1Marker : U8)
    (acc0Rent key1Limb : U64) (signer writable : U8) (lamports dataLen : U64)
    (owner0 owner1 owner2 owner3 : U64) (executable : U8) (acc1RentWord : U64)
    (acc2Marker : U8) (key2Word : U64) (acc2Signer acc2Writable : U8)
    (acc2Lamports acc2DataLen acc2Owner0 acc2Owner1 acc2Owner2 acc2Owner3 : U64)
    (acc2Executable : U8) (acc2Rent : U64) (acc3Marker : U8) (key3Word : U64)
    (acc3Signer acc3Writable : U8) (acc3Lamports acc3DataLen acc3Owner0 acc3Owner1
    acc3Owner2 acc3Owner3 : U64) (acc3Executable : U8) (acc3Rent : U64) (acc4Marker : U8)
    (key4Word : U64) (acc4Signer acc4Writable : U8) (acc4Lamports acc4DataLen acc4Owner0
    acc4Owner1 acc4Owner2 acc4Owner3 : U64) (acc4Executable : U8) (acc4Rent : U64)
    (acc5Marker : U8) (key5Word : U64) (acc5Signer acc5Writable : U8)
    (acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 : U64)
    (acc5Executable : U8) (acc5Rent : U64) (acc6Marker : U8) (key6Word : U64)
    (acc6Signer acc6Writable : U8) (acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
    acc6Owner2 acc6Owner3 : U64) (acc6Executable : U8) (acc6Rent : U64)
    (acc7Marker : U8) (key7Word : U64) (acc7Signer acc7Writable : U8)
    (acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 : U64)
    (acc7Executable : U8) (acc7Rent : U64) (acc8Marker : U8) (key8Word : U64)
    (acc8Signer acc8Writable : U8) (acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
    acc8Owner2 acc8Owner3 : U64) (acc8Executable : U8) (acc8Rent : U64)
    (acc9Marker : U8) (key9Word : U64)
    (acc9Signer acc9Writable : U8)
    (acc9Lamports acc9DataLen : U64)
    (acc9Owner0 acc9Owner1 : U64)
    (acc9Owner2 acc9Owner3 : U64)
    (acc9Executable : U8) (acc9Rent : U64) : Option Mem := do
  let m₁ ← account9OwnerHiInputMem value arg0 key0Limb acc1Marker acc0Rent key1Limb
      signer writable lamports dataLen owner0 owner1 owner2 owner3 executable acc1RentWord
      acc2Marker key2Word acc2Signer acc2Writable acc2Lamports acc2DataLen acc2Owner0 acc2Owner1
      acc2Owner2 acc2Owner3 acc2Executable acc2Rent acc3Marker key3Word acc3Signer acc3Writable
      acc3Lamports acc3DataLen acc3Owner0 acc3Owner1 acc3Owner2 acc3Owner3 acc3Executable acc3Rent
      acc4Marker key4Word acc4Signer acc4Writable acc4Lamports acc4DataLen acc4Owner0 acc4Owner1
      acc4Owner2 acc4Owner3 acc4Executable acc4Rent acc5Marker key5Word acc5Signer acc5Writable
      acc5Lamports acc5DataLen acc5Owner0 acc5Owner1 acc5Owner2 acc5Owner3 acc5Executable acc5Rent
      acc6Marker key6Word acc6Signer acc6Writable acc6Lamports acc6DataLen acc6Owner0 acc6Owner1
      acc6Owner2 acc6Owner3 acc6Executable acc6Rent acc7Marker key7Word acc7Signer acc7Writable
      acc7Lamports acc7DataLen acc7Owner0 acc7Owner1 acc7Owner2 acc7Owner3 acc7Executable acc7Rent
      acc8Marker key8Word acc8Signer acc8Writable acc8Lamports acc8DataLen acc8Owner0 acc8Owner1
      acc8Owner2 acc8Owner3 acc8Executable acc8Rent acc9Marker key9Word acc9Signer acc9Writable
      acc9Lamports acc9DataLen acc9Owner0 acc9Owner1 acc9Owner2 acc9Owner3
  let m₂ ← storev .m8 m₁ account9ExecutableAddr (.vbyte acc9Executable)
  storev .m64 m₂ account9RentEpochAddr (.vlong acc9Rent)

/-- Typed nonuple skip then account-9 exec/rent: `ldxb r1,[r2+3]`; `ldxdw r2,[r2+0x2858]`. -/

def walkAccount9ExecRentAfterSkipChain? (stackOff : U16) : Option EbpfAsm := do
  let dataLenOff ← positiveOffset? account0DataLenHeaderOff
  let zeroOff ← positiveOffset? 0
  let execOff ← positiveOffset? (account0ExecutableOffset - account0HeaderOffset)
  let rentOff ← positiveOffset? (account0RentEpochOffset - account0HeaderOffset)
  return [
    .ldx .m64 .br1 .br8 dataLenOff,
    .alu64 .mov .br2 (.reg .br8),
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m64 .br1 .br2 dataLenOff,
    .alu64 .add .br2 (.imm accountHeaderToDataBytes),
    .alu64 .add .br2 (.reg .br1),
    .alu64 .add .br2 (.imm maxPermittedDataIncrease),
    .ldx .m64 .br3 .br2 zeroOff,
    .alu64 .add .br2 (.imm 8),
    .ldx .m8 .br1 .br2 execOff,
    .ldx .m64 .br4 .br2 rentOff,
    .alu64 .mov .br2 (.reg .br4),
    .st .m64 .br10 (.reg .br1) stackOff]
/-- Run nonuple skip+account-9 walk against seeded input memory. -/
def evalWalkAccount9ExecRentAfterSkipChainToStack? (stackOff : U16) (memory : Mem) :
    Option (RegMap × Mem) := do
  let frag ← walkAccount9ExecRentAfterSkipChain? stackOff
  let state0 := initBpfState account0WalkRegs memory 64 version
  let after := runDecodedFrom 0 frag state0
  match after with
  | .ok _ regs mem _ _ _ _ _ => some (regs, mem)
  | .success _ | .eflag | .err => none

/-- Absolute `r6`-relative loads of account-9 executable and rent_epoch. -/
def evalAbsAccount9ExecRent? (memory : Mem) : Option (U8 × U64) := do
  let executable ← loadv .m8 memory account9ExecutableAddr
  let rentEpoch ← loadv .m64 memory account9RentEpochAddr
  match executable, rentEpoch with
  | .vbyte e, .vlong r => some (e, r)
  | _, _ => none

theorem walkAccount9ExecRentAfterSkipChain_verified :
    (walkAccount9ExecRentAfterSkipChain? rhsStackOffset).isSome = true := by
  native_decide

/-- Concrete nonuple skip+exec/rent: executable=`1`, rent=`0xF4`, executable staged at `[r10-16]`. -/
theorem evalWalkAccount9_after_skip_executable_1_rent_0xF4 :
    (do
      let mem ← account9ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 1 1000 128
          0xA1 0xB2 0xC3 0xD4 1 0xEE account0NonDupMarker 0x72 1 1 2000 64 0xE5 0xF6 0x17 0x28 1 0xEE
          account0NonDupMarker 0x73 1 1 3000 96 0xE6 0xF7 0x18 0x29 1 0xEE account0NonDupMarker 0x74 1 1 4000 112 0xE7 0xF8 0x19 0x2A 1 0xEF account0NonDupMarker 0x75 1 1 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 account0NonDupMarker 0x76 1 1 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 account0NonDupMarker 0x77 1 1 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 account0NonDupMarker 0x78 1 1 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3 account0NonDupMarker
          0x79 1 1 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4
      let (regs, finalMem) ← evalWalkAccount9ExecRentAfterSkipChainToStack? rhsStackOffset mem
      pure (regs .br1 == 1 && regs .br2 == 0xF4 &&
        loadv .m64 finalMem rhsStackAddr == some (.vlong 1))) =
      some true := by
  native_decide

/-- Walked account-9 exec/rent after skip chain agrees with absolute `r6`-relative loads. -/
theorem walkAccount9ExecRentAfterSkipChain_eq_absLoad :
    (do
      let mem ← account9ExecRentInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
          0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAC 0x72 1 0 2000 64 0xE5 0xF6 0x17 0x28 0 0xEE 0xAB 0x73 1 0 3000 96 0xE6 0xF7 0x18 0x29 0 0xEE 0xAD 0x74 1 0 4000 112 0xE7 0xF8 0x19 0x2A 0 0xEF 0xAF 0x75 1 0 5000 128 0xE8 0xF9 0x1A 0x2B 1 0xF0 0xB1 0x76 1 0 6000 144 0xE9 0xFA 0x1B 0x2C 1 0xF1 0xB2 0x77 1 0 7000 160 0xEA 0xFB 0x1C 0x2D 1 0xF2 0xB4 0x78 1 0 8000 176 0xEB 0xFC 0x1D 0x2E 1 0xF3
          0xB6 0x79 1 0 9000 192 0xEC 0xFD 0x1E 0x2F 1 0xF4
      let (regs, _) ← evalWalkAccount9ExecRentAfterSkipChainToStack? rhsStackOffset mem
      let (executable, rent) ← evalAbsAccount9ExecRent? mem
      pure (regs .br1 == executable.setWidth 64 && regs .br2 == rent &&
        executable == 1 && rent == 0xF4)) =
      some true := by
  native_decide
