import ProofForge.Svm.Solanalib

/-!
# Parametric Loader-v3 skip-chain lemma (prototype)

One universally quantified theorem for the `emitSkipAccount` cursor walk that E∞ knives 9, 16,
…, 135 restate per account with concrete literals and `native_decide`.

Covered: the six-instruction skip block repeated `n` times from an account header cursor in
`r2`, under Solanalib's `step` semantics, over any memory that holds each account's `data_len`
and rent word where the block reads them. Not covered: the field arcs (key, flags, lamports,
owner, executable), the initial `r8 → r2` handoff of knife 9, the `emitSkipAccount` align-8
branch (the knives seed `data_len = 0`, so their header arithmetic has no alignment term and
neither does `accountHeaderAddr`), syscalls, CPI, or ELF acceptance.
-/

namespace ProofForge.Svm.Solanalib

open _root_.Solanalib.SBPF

/-! ## The skip block -/

/-- `ACC0_DATA_LEN - ACC0_HEADER` as the 16-bit displacement the knives pass to `ldx`. -/
def dataLenOff : U16 := BitVec.ofNat 16 account0DataLenHeaderOff

/-- Displacement of the rent word read through the advanced cursor. -/
def zeroOff : U16 := 0

/-- One `emitSkipAccount` step with the header cursor already in `r2`: load `data_len`, advance
by header bytes + `data_len` + `MAX_PERMITTED_DATA_INCREASE`, read the rent word, step over it. -/
def skipBlock : List BpfInstruction := [
  .ldx .m64 .br1 .br2 dataLenOff,
  .alu64 .add .br2 (.imm accountHeaderToDataBytes),
  .alu64 .add .br2 (.reg .br1),
  .alu64 .add .br2 (.imm maxPermittedDataIncrease),
  .ldx .m64 .br3 .br2 zeroOff,
  .alu64 .add .br2 (.imm 8)]

/-- `n` consecutive skip blocks. -/
def skipChain : Nat → List BpfInstruction
  | 0 => []
  | n + 1 => skipBlock ++ skipChain n

/-! ## Memory shape and target address -/

/-- The two words one skip block reads from an account. -/
structure SkipAccount where
  dataLen : U64
  rentEpoch : U64

/-- Bytes from one account header to the next (`accountHeaderToDataBytes + data_len +
maxPermittedDataIncrease + 8`, no alignment term, matching `account<i+1>HeaderOffset =
account<i>RentEpochOffset + 8` in the knives). -/
def accountSpan (dataLen : U64) : U64 :=
  BitVec.ofNat 64 accountHeaderToDataBytes + dataLen + BitVec.ofNat 64 maxPermittedDataIncrease + 8

def spanSum (dataLens : List U64) : U64 :=
  dataLens.foldr (fun dataLen acc => accountSpan dataLen + acc) 0

/-- Absolute header address of account `i`: the account-0 header plus the spans of accounts
`j < i`. -/
def accountHeaderAddr (dataLens : List U64) (i : Nat) : U64 :=
  account0HeaderAddr + spanSum (dataLens.take i)

/-- Memory holds, for each listed account in turn from header `hdr`, its `data_len` word at
`hdr + dataLenOff` and its rent word at `hdr + accountHeaderToDataBytes + data_len +
maxPermittedDataIncrease`. This is exactly the two loads the block performs; the knife seeders
(`account…SkipNextInputMem`) build memories of this shape with `data_len = 0`. -/
def WellFormed (mem : Mem) : U64 → List SkipAccount → Prop
  | _, [] => True
  | hdr, account :: rest =>
      loadv .m64 mem (hdr + BitVec.ofNat 64 account0DataLenHeaderOff) =
          some (.vlong account.dataLen) ∧
      loadv .m64 mem (hdr + BitVec.ofNat 64 accountHeaderToDataBytes + account.dataLen +
          BitVec.ofNat 64 maxPermittedDataIncrease) = some (.vlong account.rentEpoch) ∧
      WellFormed mem (hdr + accountSpan account.dataLen) rest

/-- Register file after one skip block: `r1` = `data_len`, `r3` = rent word, `r2` advanced. -/
def blockRegs (rs : RegMap) (account : SkipAccount) : RegMap :=
  setReg (setReg (setReg rs .br1 account.dataLen) .br3 account.rentEpoch) .br2
    (rs .br2 + accountSpan account.dataLen)

def chainRegs (rs : RegMap) : List SkipAccount → RegMap
  | [] => rs
  | account :: rest => chainRegs (blockRegs rs account) rest

/-- `r6` = input base, `r2` = account-0 header cursor (the state knife 9 reaches after its
`mov r2, r8`). -/
def skipEntryRegs : RegMap :=
  setReg (setReg initRegMap .br6 mmInputStart) .br2 account0HeaderAddr

/-! ## Instruction lookup inside a chain -/

theorem skipChain_length (n : Nat) : (skipChain n).length = 6 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [skipChain, skipBlock, ih, Nat.mul_succ]

theorem decodedInstructionAt?_skipBlock_append (rest : EbpfAsm) (t : Nat) :
    decodedInstructionAt? (skipBlock ++ rest) (6 + t) = decodedInstructionAt? rest t := by
  simp [skipBlock, decodedInstructionAt?, decodedSlots]

theorem decodedInstructionAt?_skipBlock_append_lt (rest : EbpfAsm) (j : Nat) (hj : j < 6) :
    decodedInstructionAt? (skipBlock ++ rest) j = decodedInstructionAt? skipBlock j := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    omega
  all_goals simp [skipBlock, decodedInstructionAt?, decodedSlots]

/-- `program` contains `skipBlock` at decoded offset `k`. -/
def HasSkipBlockAt (program : EbpfAsm) (k : Nat) : Prop :=
  ∀ j, j < 6 → decodedInstructionAt? program (k + j) = decodedInstructionAt? skipBlock j

theorem hasSkipBlockAt_skipChain (n i : Nat) (hi : i < n) :
    HasSkipBlockAt (skipChain n) (6 * i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      intro j hj
      cases i with
      | zero =>
          rw [Nat.mul_zero, Nat.zero_add, skipChain]
          exact decodedInstructionAt?_skipBlock_append_lt (skipChain n) j hj
      | succ i =>
          rw [show 6 * (i + 1) + j = 6 + (6 * i + j) by omega, skipChain,
            decodedInstructionAt?_skipBlock_append]
          exact ih i (by omega) j hj

theorem decodedInstructionAt?_skipChain_end (n t : Nat) :
    decodedInstructionAt? (skipChain n) (6 * n + t) = none := by
  induction n with
  | zero => simp [skipChain, decodedInstructionAt?]
  | succ n ih =>
      rw [show 6 * (n + 1) + t = 6 + (6 * n + t) by omega, skipChain,
        decodedInstructionAt?_skipBlock_append, ih]

/-! ## Sequencing -/

theorem runDecodedFrom_go_step (program : EbpfAsm) (basePC k fuel : Nat) (pc : U64) (rs : RegMap)
    (mem : Mem) (ss : StackState) (sv : SBPFV) (fm : FuncMap) (cu rem : U64)
    (instruction : BpfInstruction) (hpc : pc.toNat = basePC + k)
    (hins : decodedInstructionAt? program k = some instruction) :
    runDecodedFrom.go basePC program (fuel + 1) (.ok pc rs mem ss sv fm cu rem) =
      runDecodedFrom.go basePC program fuel
        (stepDecoded instruction (.ok pc rs mem ss sv fm cu rem)) := by
  simp [runDecodedFrom.go, hpc, hins]
  intro h
  omega

theorem runDecodedFrom_go_stuck (program : EbpfAsm) (basePC k fuel : Nat) (pc : U64) (rs : RegMap)
    (mem : Mem) (ss : StackState) (sv : SBPFV) (fm : FuncMap) (cu rem : U64)
    (hpc : pc.toNat = basePC + k) (hins : decodedInstructionAt? program k = none) :
    runDecodedFrom.go basePC program fuel (.ok pc rs mem ss sv fm cu rem) =
      .ok pc rs mem ss sv fm cu rem := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [runDecodedFrom.go, hpc, hins]

@[simp] theorem setReg_apply_same (rs : RegMap) (r : BpfIReg) (v : U64) :
    setReg rs r v r = v := by
  simp [setReg]

@[simp] theorem setReg_apply_ne (rs : RegMap) (r r' : BpfIReg) (v : U64) (h : r' ≠ r) :
    setReg rs r v r' = rs r' := by
  simp [setReg, h]

private theorem add_six (x : U64) : x + 1 + 1 + 1 + 1 + 1 + 1 = x + 6 := by
  simp [BitVec.add_assoc]

theorem blockRegs_eq (rs : RegMap) (account : SkipAccount) :
    setReg (setReg (setReg (setReg (setReg (setReg rs .br1 account.dataLen) .br2
        (rs .br2 + BitVec.ofNat 64 accountHeaderToDataBytes)) .br2
        (rs .br2 + BitVec.ofNat 64 accountHeaderToDataBytes + account.dataLen)) .br2
        (rs .br2 + BitVec.ofNat 64 accountHeaderToDataBytes + account.dataLen +
          BitVec.ofNat 64 maxPermittedDataIncrease)) .br3 account.rentEpoch) .br2
        (rs .br2 + BitVec.ofNat 64 accountHeaderToDataBytes + account.dataLen +
          BitVec.ofNat 64 maxPermittedDataIncrease + 8) =
      blockRegs rs account := by
  funext r
  cases r <;> simp [setReg, blockRegs, accountSpan, BitVec.add_assoc]

private theorem dataLenOff_signExtend :
    dataLenOff.signExtend 64 = BitVec.ofNat 64 account0DataLenHeaderOff := by
  decide

private theorem zeroOff_signExtend : zeroOff.signExtend 64 = 0#64 := by
  decide

private theorem headerToData_signExtend :
    (BitVec.ofNat 32 accountHeaderToDataBytes).signExtend 64 =
      BitVec.ofNat 64 accountHeaderToDataBytes := by
  decide

private theorem maxIncrease_signExtend :
    (BitVec.ofNat 32 maxPermittedDataIncrease).signExtend 64 =
      BitVec.ofNat 64 maxPermittedDataIncrease := by
  decide

private theorem eight_signExtend : (8#32).signExtend 64 = (8 : U64) := by
  decide

private theorem toNat_add_one (pc : U64) (m : Nat) (hpc : pc.toNat = m) (hfit : m + 1 < 2 ^ 64) :
    (pc + 1).toNat = m + 1 := by
  rw [BitVec.toNat_add, hpc]
  simp
  omega

private theorem toNat_add_six (pc : U64) (m : Nat) (hpc : pc.toNat = m) (hfit : m + 6 < 2 ^ 64) :
    (pc + 6).toNat = m + 6 := by
  rw [BitVec.toNat_add, hpc]
  simp
  omega

/-- One skip block, executed by PC dispatch inside any `program` that contains it at offset
`k`, advances the cursor by `accountSpan` and consumes exactly six fuel. -/
theorem runDecodedFrom_go_skipBlock (program : EbpfAsm) (basePC k fuel : Nat) (pc : U64)
    (rs : RegMap) (mem : Mem) (ss : StackState) (sv : SBPFV) (fm : FuncMap) (cu rem : U64)
    (account : SkipAccount) (hblock : HasSkipBlockAt program k)
    (hpc : pc.toNat = basePC + k) (hfit : basePC + k + 6 < 2 ^ 64)
    (hlen : loadv .m64 mem (rs .br2 + BitVec.ofNat 64 account0DataLenHeaderOff) =
      some (.vlong account.dataLen))
    (hrent : loadv .m64 mem (rs .br2 + BitVec.ofNat 64 accountHeaderToDataBytes +
      account.dataLen + BitVec.ofNat 64 maxPermittedDataIncrease) =
      some (.vlong account.rentEpoch)) :
    runDecodedFrom.go basePC program (fuel + 6) (.ok pc rs mem ss sv fm cu rem) =
      runDecodedFrom.go basePC program fuel
        (.ok (pc + 6) (blockRegs rs account) mem ss sv fm (cu + 6) rem) := by
  have h0 := hblock 0 (by omega)
  have h1 := hblock 1 (by omega)
  have h2 := hblock 2 (by omega)
  have h3 := hblock 3 (by omega)
  have h4 := hblock 4 (by omega)
  have h5 := hblock 5 (by omega)
  simp [skipBlock, decodedInstructionAt?, decodedSlots] at h0 h1 h2 h3 h4 h5
  have hpc1 : (pc + 1).toNat = basePC + (k + 1) :=
    toNat_add_one pc (basePC + k) hpc (by omega)
  have hpc2 : (pc + 1 + 1).toNat = basePC + (k + 2) :=
    toNat_add_one _ (basePC + (k + 1)) hpc1 (by omega)
  have hpc3 : (pc + 1 + 1 + 1).toNat = basePC + (k + 3) :=
    toNat_add_one _ (basePC + (k + 2)) hpc2 (by omega)
  have hpc4 : (pc + 1 + 1 + 1 + 1).toNat = basePC + (k + 4) :=
    toNat_add_one _ (basePC + (k + 3)) hpc3 (by omega)
  have hpc5 : (pc + 1 + 1 + 1 + 1 + 1).toNat = basePC + (k + 5) :=
    toNat_add_one _ (basePC + (k + 4)) hpc4 (by omega)
  rw [show fuel + 6 = fuel + 5 + 1 from rfl,
    runDecodedFrom_go_step program basePC k _ _ _ _ _ _ _ _ _ _ hpc h0]
  simp only [stepDecoded, step, evalLoad, dataLenOff_signExtend, hlen]
  rw [runDecodedFrom_go_step program basePC (k + 1) _ _ _ _ _ _ _ _ _ _ hpc1 h1]
  simp only [stepDecoded, step, stepRegOutcome, evalAlu64, sndOp64, headerToData_signExtend,
    setReg_apply_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [runDecodedFrom_go_step program basePC (k + 2) _ _ _ _ _ _ _ _ _ _ hpc2 h2]
  simp only [stepDecoded, step, stepRegOutcome, evalAlu64, sndOp64,
    setReg_apply_same, setReg_apply_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [runDecodedFrom_go_step program basePC (k + 3) _ _ _ _ _ _ _ _ _ _ hpc3 h3]
  simp only [stepDecoded, step, stepRegOutcome, evalAlu64, sndOp64, maxIncrease_signExtend,
    setReg_apply_same]
  rw [runDecodedFrom_go_step program basePC (k + 4) _ _ _ _ _ _ _ _ _ _ hpc4 h4]
  simp only [stepDecoded, step, evalLoad, zeroOff_signExtend, BitVec.add_zero,
    setReg_apply_same, hrent]
  rw [runDecodedFrom_go_step program basePC (k + 5) _ _ _ _ _ _ _ _ _ _ hpc5 h5]
  simp only [stepDecoded, step, stepRegOutcome, evalAlu64, sndOp64, eight_signExtend,
    setReg_apply_same, setReg_apply_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [blockRegs_eq, add_six pc, add_six cu]

theorem blockRegs_br2 (rs : RegMap) (account : SkipAccount) :
    blockRegs rs account .br2 = rs .br2 + accountSpan account.dataLen := by
  simp [blockRegs]

theorem blockRegs_other (rs : RegMap) (account : SkipAccount) (r : BpfIReg)
    (h1 : r ≠ .br1) (h2 : r ≠ .br2) (h3 : r ≠ .br3) :
    blockRegs rs account r = rs r := by
  simp [blockRegs, setReg, h1, h2, h3]

theorem chainRegs_br2 (rs : RegMap) (accounts : List SkipAccount) :
    chainRegs rs accounts .br2 = rs .br2 + spanSum (accounts.map SkipAccount.dataLen) := by
  induction accounts generalizing rs with
  | nil => simp [chainRegs, spanSum]
  | cons account rest ih =>
      rw [chainRegs, ih, blockRegs_br2]
      simp [spanSum, BitVec.add_assoc]

theorem chainRegs_other (rs : RegMap) (accounts : List SkipAccount) (r : BpfIReg)
    (h1 : r ≠ .br1) (h2 : r ≠ .br2) (h3 : r ≠ .br3) :
    chainRegs rs accounts r = rs r := by
  induction accounts generalizing rs with
  | nil => rfl
  | cons account rest ih => rw [chainRegs, ih, blockRegs_other rs account r h1 h2 h3]

private theorem ofNat_six_mul_succ (n : Nat) :
    (BitVec.ofNat 64 (6 * (n + 1)) : U64) = 6 + BitVec.ofNat 64 (6 * n) := by
  rw [Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add]
  rfl

/-- `accounts.length` skip blocks, executed by PC dispatch inside any `program` that contains
them consecutively from offset `k`, over a memory well-formed from the cursor in `r2`. -/
theorem runDecodedFrom_go_skipChain (program : EbpfAsm) (basePC k fuel : Nat) (pc : U64)
    (rs : RegMap) (mem : Mem) (ss : StackState) (sv : SBPFV) (fm : FuncMap) (cu rem : U64)
    (accounts : List SkipAccount)
    (hblocks : ∀ i, i < accounts.length → HasSkipBlockAt program (k + 6 * i))
    (hpc : pc.toNat = basePC + k) (hfit : basePC + k + 6 * accounts.length < 2 ^ 64)
    (hwf : WellFormed mem (rs .br2) accounts) :
    runDecodedFrom.go basePC program (fuel + 6 * accounts.length) (.ok pc rs mem ss sv fm cu rem) =
      runDecodedFrom.go basePC program fuel
        (.ok (pc + BitVec.ofNat 64 (6 * accounts.length)) (chainRegs rs accounts) mem ss sv fm
          (cu + BitVec.ofNat 64 (6 * accounts.length)) rem) := by
  induction accounts generalizing k pc rs cu with
  | nil => simp [chainRegs]
  | cons account rest ih =>
      obtain ⟨hlen, hrent, hrest⟩ := hwf
      have hblock : HasSkipBlockAt program k := by simpa using hblocks 0 (by simp)
      rw [List.length_cons, show fuel + 6 * (rest.length + 1) = fuel + 6 * rest.length + 6 by
        omega, runDecodedFrom_go_skipBlock program basePC k _ pc rs mem ss sv fm cu rem account
        hblock hpc (by simp at hfit; omega) hlen hrent]
      rw [ih (k + 6) (pc + 6) (blockRegs rs account) (cu + 6)
        (fun i hi => by
          have := hblocks (i + 1) (by simp; omega)
          rwa [show k + 6 * (i + 1) = k + 6 + 6 * i by omega] at this)
        (by rw [toNat_add_six pc (basePC + k) hpc (by simp at hfit; omega)]; omega)
        (by simp at hfit; omega)
        (by rw [blockRegs_br2]; exact hrest)]
      rw [chainRegs, ofNat_six_mul_succ, ← BitVec.add_assoc, ← BitVec.add_assoc]

/-! ## The parametric skip-chain lemma -/

/-- Register file `initBpfState` installs from `skipEntryRegs`. -/
def skipStartRegs : RegMap :=
  setReg skipEntryRegs .br10 (mmStackStart + stackFrameSize * maxCallDepth)

theorem accountHeaderAddr_length (dataLens : List U64) :
    accountHeaderAddr dataLens dataLens.length = account0HeaderAddr + spanSum dataLens := by
  simp [accountHeaderAddr]

/-- Running `skipChain accounts.length` from the account-0 header cursor in `r2`, over any memory
well-formed for `accounts`, halts at PC `6 * accounts.length` with memory unchanged, `r2` on the
header of account `accounts.length`, and every register other than the scratch `r1`/`r2`/`r3`
untouched. Exact register file: `chainRegs skipStartRegs accounts`. -/
theorem skipChain_lands (accounts : List SkipAccount) (mem : Mem) (fuel : U64)
    (hfit : 6 * accounts.length < 2 ^ 64)
    (hwf : WellFormed mem account0HeaderAddr accounts) :
    runDecodedFrom 0 (skipChain accounts.length) (initBpfState skipEntryRegs mem fuel version) =
      .ok (BitVec.ofNat 64 (6 * accounts.length)) (chainRegs skipStartRegs accounts) mem
        initStackState version initFuncMap (BitVec.ofNat 64 (6 * accounts.length)) fuel ∧
    chainRegs skipStartRegs accounts .br2 =
      accountHeaderAddr (accounts.map SkipAccount.dataLen) accounts.length ∧
    ∀ r, r ≠ .br1 → r ≠ .br2 → r ≠ .br3 →
      chainRegs skipStartRegs accounts r = skipStartRegs r := by
  refine ⟨?_, ?_, fun r h1 h2 h3 => chainRegs_other _ _ r h1 h2 h3⟩
  · have hstart : skipStartRegs .br2 = account0HeaderAddr := by
      simp [skipStartRegs, skipEntryRegs]
    rw [runDecodedFrom, skipChain_length, initBpfState, Nat.add_comm, ← skipStartRegs,
      runDecodedFrom_go_skipChain (skipChain accounts.length) 0 0 1 0 skipStartRegs mem
        initStackState version initFuncMap 0 fuel accounts
        (fun i hi => by simpa using hasSkipBlockAt_skipChain accounts.length i hi)
        (by simp) (by omega) (by rw [hstart]; exact hwf)]
    rw [runDecodedFrom_go_stuck (skipChain accounts.length) 0 (6 * accounts.length) 1
      _ _ _ _ _ _ _ _ (by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit])
      (decodedInstructionAt?_skipChain_end accounts.length 0)]
    simp
  · rw [chainRegs_br2, ← List.length_map (f := SkipAccount.dataLen) (as := accounts),
      accountHeaderAddr_length]
    simp [skipStartRegs, skipEntryRegs]

end ProofForge.Svm.Solanalib
