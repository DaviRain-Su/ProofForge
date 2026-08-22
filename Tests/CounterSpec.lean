import SolanaLean
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
#guard SolanaLean.IR.isCounterShape SolanaLean.IR.extractedCounter
#guard SolanaLean.IR.isCounterShape SolanaLean.IR.extractedPair
#guard SolanaLean.IR.dataLen SolanaLean.IR.extractedPair == 24
#guard SolanaLean.Profile.checkRootName "increment" == .accept
#guard (match SolanaLean.Profile.checkRootName "evil" with
  | .reject _ => true
  | .accept => false)

end Tests.CounterSpec
