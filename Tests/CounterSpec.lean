import SolanaLean
import Examples.Counter

namespace Tests.CounterSpec

open SolanaLean.Counter

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
#guard isOkValue (increment (s (u64Max - 1)) 1) u64Max
#guard get (init 7) == 7
#guard SolanaLean.IR.isCounterShape Examples.Counter.program
#guard SolanaLean.Profile.checkRootName "increment" == .accept
#guard (match SolanaLean.Profile.checkRootName "evil" with
  | .reject _ => true
  | .accept => false)

end Tests.CounterSpec
