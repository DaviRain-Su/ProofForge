import ProofForge
import Examples.Counter

namespace Tests.CounterSpec

open Examples.Counter

def s (n : UInt64) : State := { value := n }

private def isOkValue (r : Except Error (State × UInt64)) (n : UInt64) : Bool :=
  match r with
  | .ok (st, ret) => st.value == n && ret == n
  | .error _ => false

private def isOverflow (r : Except Error (State × UInt64)) : Bool :=
  match r with
  | .error .overflow => true
  | .ok _ => false

#guard isOkValue (increment (s 0) 1) 1
#guard isOkValue (increment (s 0) 0) 0
#guard isOkValue (increment (s u64Max) 0) u64Max
#guard isOverflow (increment (s u64Max) 1)
#guard isOverflow (increment (s (u64Max - 1)) 2)

#guard
  match decrement (s 5) 3 with
  | .ok (st, ret) => st.value == 2 && ret == 2
  | .error _ => false
#guard
  match decrement (s 2) 3 with
  | .error .overflow => true
  | .ok _ => false
#guard isOkValue (increment (s (u64Max - 1)) 1) u64Max
#guard get (init 7) == 7
#guard
  match scale (s 5) 3 with
  | .ok (st, ret) => st.value == 15 && ret == 15
  | .error _ => false
#guard
  match scale (s 5) 0 with
  | .ok (st, ret) => st.value == 0 && ret == 0
  | .error _ => false
#guard
  match scale (s u64Max) 2 with
  | .error .overflow => true
  | .ok _ => false
#guard
  match divide (s 8) 3 with
  | .ok (st, ret) => st.value == 2 && ret == 2
  | .error _ => false
#guard
  match divide (s 8) 0 with
  | .error .overflow => true
  | .ok _ => false
#guard
  match modulo (s 8) 3 with
  | .ok (st, ret) => st.value == 2 && ret == 2
  | .error _ => false
#guard nonzero (s 0) == 1
#guard nonzero (s 7) == 0
#guard ProofForge.Extract.Legacy.isCounterShape ProofForge.Golden.extractedCounter
#guard ProofForge.Extract.Legacy.isCounterShape ProofForge.Golden.extractedPair
#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedPair == 24
#guard ProofForge.Extract.Legacy.digestHex ProofForge.Golden.extractedCounter != ""
#guard ProofForge.Profile.checkRootName "increment" == .accept
#guard (match ProofForge.Profile.checkRootName "evil" with
  | .reject _ => true
  | .accept => false)

end Tests.CounterSpec
