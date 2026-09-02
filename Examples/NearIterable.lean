import ProofForge

namespace Examples.NearIterable

open ProofForge.Wasm.Near.Sdk.Store
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  mapLength : UInt64
  setLength : UInt64
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- N14 IterableMap Handle: capacity 3; vector `0x76504d49`, lookup `0x6d504d49` (base `IMP`). -/
@[pf_inline] def mapSlots : DirectIterableMap64.Handle :=
  DirectIterableMap64.handle 3 (0x76504d49 : Prefix4) (0x6d504d49 : Prefix4)

/-- N14 IterableSet Handle: capacity 3; vector `0x76535449`, lookup `0x6d535449` (base `ITS`). -/
@[pf_inline] def setSlots : DirectIterableSet64.Handle :=
  DirectIterableSet64.handle 3 (0x76535449 : Prefix4) (0x6d535449 : Prefix4)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { mapLength := 0, setLength := 0, marker := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def mapLen (state : State) : UInt64 :=
  state.mapLength

@[pf_entry]
def setLen (state : State) : UInt64 :=
  state.setLength

@[pf_entry]
def mapGet (_state : State) (key : UInt64) : UInt64 :=
  mapSlots.getD key 0

@[pf_entry]
def mapIndex (_state : State) (key : UInt64) : UInt64 :=
  mapSlots.indexCode key

@[pf_entry]
def mapKeyAt (state : State) (index : UInt64) : UInt64 :=
  mapSlots.keyAtD state.mapLength index 0

@[pf_entry]
def mapHasKeyAt (state : State) (index : UInt64) : UInt64 :=
  mapSlots.hasKeyAt state.mapLength index

@[pf_entry]
def setIndex (_state : State) (value : UInt64) : UInt64 :=
  setSlots.indexCode value

@[pf_entry]
def setKeyAt (state : State) (index : UInt64) : UInt64 :=
  setSlots.keyAtD state.setLength index 0

@[pf_entry]
def setHasKeyAt (state : State) (index : UInt64) : UInt64 :=
  setSlots.hasKeyAt state.setLength index

@[pf_entry]
def mapPut (state : State) (packed : UInt64) : Except Error (State × UInt64) :=
  let key := packed &&& 0xffffffff
  let value := packed >>> 32
  if state.mapLength ≤ 3 then
    let lookupResult : ResultBuffer := 12
    let _ := lookupResult.read (mapSlots.lookupKey key)
    if lookupResult.status = 0 then
      if state.mapLength < 3 then
        let vectorResult : ResultBuffer := 8
        let _ := vectorResult.write
          (mapSlots.vectorKey state.mapLength) (mapSlots.vectorValue key)
        let _ := lookupResult.write
          (mapSlots.lookupKey key) (mapSlots.lookupValue value state.mapLength)
        .ok ({
          state with
          mapLength := state.mapLength + 1
          marker := state.mapLength + 1
        }, state.mapLength + 1)
      else
        .error .overflow
    else
      if lookupResult.length = 12 then
        let index :=
          (lookupResult.byte 8).toUInt64 |||
            ((lookupResult.byte 9).toUInt64 <<< 8) |||
            ((lookupResult.byte 10).toUInt64 <<< 16) |||
            ((lookupResult.byte 11).toUInt64 <<< 24)
        if index < 3 then
          if index < state.mapLength then
            let _ := lookupResult.write
              (mapSlots.lookupKey key) (mapSlots.lookupValue value index)
            .ok ({ state with marker := state.mapLength }, state.mapLength)
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
  else
    .error .overflow

@[pf_entry]
def mapRemove (state : State) (key : UInt64) : Except Error (State × UInt64) :=
  if state.mapLength ≤ 3 then
    let lookupResult : ResultBuffer := 12
    let _ := lookupResult.read (mapSlots.lookupKey key)
    if lookupResult.status = 1 then
      if lookupResult.length = 12 then
        let index :=
          (lookupResult.byte 8).toUInt64 |||
            ((lookupResult.byte 9).toUInt64 <<< 8) |||
            ((lookupResult.byte 10).toUInt64 <<< 16) |||
            ((lookupResult.byte 11).toUInt64 <<< 24)
        if index < 3 then
          if index < state.mapLength then
            let lastIndex := state.mapLength - 1
            if index = lastIndex then
              let _ := lookupResult.remove (mapSlots.lookupKey key)
              let vectorResult : ResultBuffer := 8
              let _ := vectorResult.remove (mapSlots.vectorKey lastIndex)
              .ok ({
                state with
                mapLength := lastIndex
                marker := lastIndex
              }, lastIndex)
            else
              let vectorResult : ResultBuffer := 8
              let _ := vectorResult.read (mapSlots.vectorKey lastIndex)
              if vectorResult.status = 1 then
                if vectorResult.length = 8 then
                  let movedKey :=
                    (vectorResult.byte 0).toUInt64 |||
                      ((vectorResult.byte 1).toUInt64 <<< 8) |||
                      ((vectorResult.byte 2).toUInt64 <<< 16) |||
                      ((vectorResult.byte 3).toUInt64 <<< 24) |||
                      ((vectorResult.byte 4).toUInt64 <<< 32) |||
                      ((vectorResult.byte 5).toUInt64 <<< 40) |||
                      ((vectorResult.byte 6).toUInt64 <<< 48) |||
                      ((vectorResult.byte 7).toUInt64 <<< 56)
                  let _ := lookupResult.read (mapSlots.lookupKey movedKey)
                  if lookupResult.status = 1 then
                    if lookupResult.length = 12 then
                      let movedIndex :=
                        (lookupResult.byte 8).toUInt64 |||
                          ((lookupResult.byte 9).toUInt64 <<< 8) |||
                          ((lookupResult.byte 10).toUInt64 <<< 16) |||
                          ((lookupResult.byte 11).toUInt64 <<< 24)
                      if movedIndex = lastIndex then
                        let movedValue :=
                          (lookupResult.byte 0).toUInt64 |||
                            ((lookupResult.byte 1).toUInt64 <<< 8) |||
                            ((lookupResult.byte 2).toUInt64 <<< 16) |||
                            ((lookupResult.byte 3).toUInt64 <<< 24) |||
                            ((lookupResult.byte 4).toUInt64 <<< 32) |||
                            ((lookupResult.byte 5).toUInt64 <<< 40) |||
                            ((lookupResult.byte 6).toUInt64 <<< 48) |||
                            ((lookupResult.byte 7).toUInt64 <<< 56)
                        let _ := lookupResult.remove (mapSlots.lookupKey key)
                        let _ := vectorResult.write
                          (mapSlots.vectorKey index) (mapSlots.vectorValue movedKey)
                        let _ := lookupResult.write
                          (mapSlots.lookupKey movedKey) (mapSlots.lookupValue movedValue index)
                        let _ := vectorResult.remove (mapSlots.vectorKey lastIndex)
                        .ok ({
                          state with
                          mapLength := lastIndex
                          marker := lastIndex
                        }, lastIndex)
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else
                  .error .overflow
              else
                .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

@[pf_entry]
def setInsert (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if state.setLength ≤ 3 then
    let lookupResult : ResultBuffer := 4
    let _ := lookupResult.read (setSlots.lookupKey value)
    if lookupResult.status = 0 then
      if state.setLength < 3 then
        let vectorResult : ResultBuffer := 8
        let _ := vectorResult.write
          (setSlots.vectorKey state.setLength) (setSlots.vectorValue value)
        let _ := lookupResult.write
          (setSlots.lookupKey value) (setSlots.lookupValue state.setLength)
        .ok ({
          state with
          setLength := state.setLength + 1
          marker := state.setLength + 1
        }, state.setLength + 1)
      else
        .error .overflow
    else
      if lookupResult.length = 4 then
        let index :=
          (lookupResult.byte 0).toUInt64 |||
            ((lookupResult.byte 1).toUInt64 <<< 8) |||
            ((lookupResult.byte 2).toUInt64 <<< 16) |||
            ((lookupResult.byte 3).toUInt64 <<< 24)
        if index < 3 then
          if index < state.setLength then
            .ok ({ state with marker := state.setLength }, state.setLength)
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
  else
    .error .overflow

@[pf_entry]
def setRemove (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  if state.setLength ≤ 3 then
    let lookupResult : ResultBuffer := 4
    let _ := lookupResult.read (setSlots.lookupKey value)
    if lookupResult.status = 1 then
      if lookupResult.length = 4 then
        let index :=
          (lookupResult.byte 0).toUInt64 |||
            ((lookupResult.byte 1).toUInt64 <<< 8) |||
            ((lookupResult.byte 2).toUInt64 <<< 16) |||
            ((lookupResult.byte 3).toUInt64 <<< 24)
        if index < 3 then
          if index < state.setLength then
            let lastIndex := state.setLength - 1
            if index = lastIndex then
              let _ := lookupResult.remove (setSlots.lookupKey value)
              let vectorResult : ResultBuffer := 8
              let _ := vectorResult.remove (setSlots.vectorKey lastIndex)
              .ok ({
                state with
                setLength := lastIndex
                marker := lastIndex
              }, lastIndex)
            else
              let vectorResult : ResultBuffer := 8
              let _ := vectorResult.read (setSlots.vectorKey lastIndex)
              if vectorResult.status = 1 then
                if vectorResult.length = 8 then
                  let movedValue :=
                    (vectorResult.byte 0).toUInt64 |||
                      ((vectorResult.byte 1).toUInt64 <<< 8) |||
                      ((vectorResult.byte 2).toUInt64 <<< 16) |||
                      ((vectorResult.byte 3).toUInt64 <<< 24) |||
                      ((vectorResult.byte 4).toUInt64 <<< 32) |||
                      ((vectorResult.byte 5).toUInt64 <<< 40) |||
                      ((vectorResult.byte 6).toUInt64 <<< 48) |||
                      ((vectorResult.byte 7).toUInt64 <<< 56)
                  let _ := lookupResult.read (setSlots.lookupKey movedValue)
                  if lookupResult.status = 1 then
                    if lookupResult.length = 4 then
                      let movedIndex :=
                        (lookupResult.byte 0).toUInt64 |||
                          ((lookupResult.byte 1).toUInt64 <<< 8) |||
                          ((lookupResult.byte 2).toUInt64 <<< 16) |||
                          ((lookupResult.byte 3).toUInt64 <<< 24)
                      if movedIndex = lastIndex then
                        let _ := lookupResult.remove (setSlots.lookupKey value)
                        let _ := vectorResult.write
                          (setSlots.vectorKey index) (setSlots.vectorValue movedValue)
                        let _ := lookupResult.write
                          (setSlots.lookupKey movedValue) (setSlots.lookupValue index)
                        let _ := vectorResult.remove (setSlots.vectorKey lastIndex)
                        .ok ({
                          state with
                          setLength := lastIndex
                          marker := lastIndex
                        }, lastIndex)
                      else
                        .error .overflow
                    else
                      .error .overflow
                  else
                    .error .overflow
                else
                  .error .overflow
              else
                .error .overflow
          else
            .error .overflow
        else
          .error .overflow
      else
        .error .overflow
    else
      .error .overflow
  else
    .error .overflow

/-- Install an out-of-capacity map index for fail-closed sandbox coverage. -/
@[pf_entry]
def corruptMap7 (state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 12
  let _ := result.write
    (mapSlots.lookupKey 7) (mapSlots.lookupValue 700 3)
  .ok ({ state with marker := 77 }, 77)

/-- Install an out-of-capacity set index for fail-closed sandbox coverage. -/
@[pf_entry]
def corruptSet5 (state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 4
  let _ := result.write
    (setSlots.lookupKey 5) (setSlots.lookupValue 3)
  .ok ({ state with marker := 55 }, 55)

end Examples.NearIterable
