import Examples.Svm.InstructionsSlice
import ProofForge

/-!
Geometry and extraction checks for svm-rt-004 bounded Instructions / fixed-offset sliced sysvar.
-/

namespace Tests.InstructionsSliceSpec

open ProofForge.Svm.Sdk

#guard Sysvar.instructionsKey ==
  Pubkey.ofWords 7408838205410486022 13889942742359136821
    11922530290679293121 35966925531

#guard (Sysvar.Instructions.view (Account.Handle.at 1) 24).wellFormed
#guard !(Sysvar.Instructions.view (Account.Handle.at 1) 1).wellFormed
#guard (Sysvar.Slice.accountData (Account.Handle.at 1) 8 8).wellFormed
#guard !(Sysvar.Slice.accountData (Account.Handle.at 1) 1 8).wellFormed
#guard !(Sysvar.Slice.accountData (Account.Handle.at 1) 0 0).wellFormed
#guard Examples.Svm.InstructionsSlice.serializedBytesNat = 24
#guard Examples.Svm.InstructionsSlice.serializedBytes = 24

#pf_build Examples.Svm.InstructionsSlice

end Tests.InstructionsSliceSpec
