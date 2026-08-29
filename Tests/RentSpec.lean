import Examples.Rent

namespace Tests.RentSpec

open Examples.Rent
open ProofForge.Svm.Sdk

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard exempt (init 0) == Sysvar.Rent.minimumBalance 16

#guard
  match stamp (init 0) with
  | .ok (st, ret) =>
      st.dummy == Sysvar.Rent.minimumBalance 16 && ret == Sysvar.Rent.minimumBalance 16
  | .error _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedRent with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_rent_sysvar" &&
        asm.contains "load rentExemption 16" &&
        asm.contains "call exempt" &&
        asm.contains "call stamp"

end Tests.RentSpec
