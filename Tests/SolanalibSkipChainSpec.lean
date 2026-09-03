import ProofForge.Svm.SolanalibSkipChain

namespace Tests.SolanalibSkipChainSpec

open ProofForge.Svm.Solanalib
open _root_.Solanalib.SBPF

example : accountHeaderAddr [0] 1 = account1HeaderAddr := by decide
example : accountHeaderAddr [0, 0] 2 = account2HeaderAddr := by decide
example : accountHeaderAddr [0, 0, 0] 3 = account3HeaderAddr := by decide
example : accountHeaderAddr [0, 0, 0] 3 = mmInputStart + BitVec.ofNat 64 (0x8 + 3 * 0x2860) := by
  decide
example : accountHeaderAddr [128, 64, 96] 3 =
    mmInputStart + BitVec.ofNat 64 (0x8 + 3 * 0x2860 + 128 + 64 + 96) := by
  decide

#guard (skipChain 3).length == 18

private def seedWord (addr word : U64) (mem : Mem) : Mem :=
  (storev .m64 mem addr (.vlong word)).getD mem

/-- Three zero-`data_len` accounts seeded at the knife-16/17 addresses. -/
private def zeroAccounts : List SkipAccount := [⟨0, 0xEE⟩, ⟨0, 0xEF⟩, ⟨0, 0xF0⟩]

private def zeroMem : Mem :=
  seedWord account0DataLenAddr 0 <| seedWord account0RentEpochAddr 0xEE <|
  seedWord account1DataLenAddr 0 <| seedWord account1RentEpochAddr 0xEF <|
  seedWord account2DataLenAddr 0 <| seedWord account2RentEpochAddr 0xF0 initMem

private def runChain (accounts : List SkipAccount) (mem : Mem) : Option (U64 × U64) :=
  match runDecodedFrom 0 (skipChain accounts.length)
      (initBpfState skipEntryRegs mem 64 version) with
  | .ok pc regs _ _ _ _ _ _ => some (pc, regs .br2)
  | .success _ | .eflag | .err => none

#guard runChain zeroAccounts zeroMem == some (18, account3HeaderAddr)

/-- Knife 16's own seeded memory (`walkAccount1SkipNextAfterAccount0Skip_eq_absLoad`). -/
private def knife16Mem : Option Mem :=
  account1SkipNextInputMem 7 5 0x42 account0NonDupMarker 0xEE 0x71 1 0 1000 128
    0xA1 0xB2 0xC3 0xD4 0 0xEE 0xAB

#guard (knife16Mem >>= runChain [⟨0, 0xEE⟩, ⟨0, 0xEE⟩]) == some (12, account2HeaderAddr)

private theorem zeroMem_wellFormed : WellFormed zeroMem account0HeaderAddr zeroAccounts := by
  simp only [WellFormed, zeroAccounts]
  decide

/-- The general lemma instantiated at `n = 3` reproduces knife 17's account-3 header address. -/
example :
    (runDecodedFrom 0 (skipChain 3) (initBpfState skipEntryRegs zeroMem 64 version) =
      .ok 18 (chainRegs skipStartRegs zeroAccounts) zeroMem initStackState version initFuncMap
        18 64) ∧
    chainRegs skipStartRegs zeroAccounts .br2 = account3HeaderAddr := by
  obtain ⟨hrun, hbr2, _⟩ := skipChain_lands zeroAccounts zeroMem 64 (by decide) zeroMem_wellFormed
  exact ⟨hrun, by rw [hbr2]; decide⟩

/-- Non-zero `data_len`s, which no knife covers. -/
private def mixedAccounts : List SkipAccount := [⟨128, 0xEE⟩, ⟨64, 0xEF⟩, ⟨96, 0xF0⟩]

private def mixedMem : Mem :=
  let hdr0 := account0HeaderAddr
  let hdr1 := hdr0 + accountSpan 128
  let hdr2 := hdr1 + accountSpan 64
  seedWord (hdr0 + 0x50) 128 <| seedWord (hdr0 + 88 + 128 + 0x2800) 0xEE <|
  seedWord (hdr1 + 0x50) 64 <| seedWord (hdr1 + 88 + 64 + 0x2800) 0xEF <|
  seedWord (hdr2 + 0x50) 96 <| seedWord (hdr2 + 88 + 96 + 0x2800) 0xF0 initMem

#guard runChain mixedAccounts mixedMem == some (18, accountHeaderAddr [128, 64, 96] 3)
#guard runChain mixedAccounts mixedMem ==
  some (18, mmInputStart + BitVec.ofNat 64 (0x8 + 3 * 0x2860 + 128 + 64 + 96))

end Tests.SolanalibSkipChainSpec
