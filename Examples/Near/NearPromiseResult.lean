import ProofForge

namespace Examples.Near.NearPromiseResult
open ProofForge.Wasm.Near.Sdk

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { marker := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

/-- Ordinary calls have no callback inputs and therefore report zero. -/
@[pf_entry]
def resultsCount (_state : State) : Except Error (State × UInt64) :=
  let count := Promises.resultsCount
  .ok ({ marker := count }, count)

/-- Read callback input zero. Calling this as an ordinary transaction aborts out of range. -/
@[pf_entry]
def resultStatus (_state : State) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let status := result.status
  .ok ({ marker := status }, status)

@[pf_entry]
def resultLength (_state : State) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let length := result.length
  .ok ({ marker := length }, length)

@[pf_entry]
def resultFits (_state : State) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  if result.fits then
    .ok ({ marker := 1 }, 1)
  else
    .ok ({ marker := 0 }, 0)

@[pf_entry]
def resultByte (_state : State) (index : UInt64) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let byte := (result.byte index).toUInt64
  .ok ({ marker := byte }, byte)

/-- Smaller descriptor for the later genuine-callback oversized-result sandbox scene. -/
@[pf_entry]
def smallResultLength (_state : State) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 4
  let _ := result.read 0
  let length := result.length
  .ok ({ marker := length }, length)

@[pf_entry]
def smallResultFits (_state : State) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 4
  let _ := result.read 0
  if result.fits then
    .ok ({ marker := 1 }, 1)
  else
    .ok ({ marker := 0 }, 0)

end Examples.Near.NearPromiseResult