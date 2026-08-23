import Examples.Seat
import ProofForge

namespace Tests.SeatSpec

open Examples.Seat
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == findPda "vault"

#guard
  match openSeat (init 0) 1000 with
  | .ok (_, ret) => ret == 1000
  | .error _ => false

#guard
  match openBase (init 0) with
  | .ok (_, ret) => ret == 0
  | .error _ => false

end Tests.SeatSpec
