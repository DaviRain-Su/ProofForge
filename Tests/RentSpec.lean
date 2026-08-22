import Examples.Rent

namespace Tests.RentSpec

open Examples.Rent
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard exempt (init 0) == rentExemption 16

#guard
  match stamp (init 0) with
  | .ok (st, ret) => st.dummy == rentExemption 16 && ret == rentExemption 16
  | .error _ => false

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedRent with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_rent_sysvar" &&
        asm.contains "load rentExemption 16" &&
        asm.contains "call exempt" &&
        asm.contains "call stamp"

end Tests.RentSpec
