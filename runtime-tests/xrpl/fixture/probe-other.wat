;; Probe set_data_object_field targeting a hardcoded other AccountID.
;; Not setUserData (that name does not exist). Not Sdk.Map.
;; Other = rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG
;;   20B = d0bc2a540b15411f44a24dfb58d23ad5d9d9b350
;; Key "bal", UINT64 STI 3 value 1.
(module
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 0)
    "\d0\bc\2a\54\0b\15\41\1f\44\a2\4d\fb\58\d2\3a\d5\d9\d9\b3\50")
  (data (i32.const 64) "bal")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (i32.store8 (i32.const 28) (i32.const 3))
    (i32.store8 (i32.const 29) (i32.const 0))
    (i32.store8 (i32.const 30) (i32.const 0))
    (i32.store8 (i32.const 31) (i32.const 0))
    (i32.store8 (i32.const 32) (i32.const 0))
    (i32.store8 (i32.const 33) (i32.const 0))
    (i32.store8 (i32.const 34) (i32.const 0))
    (i32.store8 (i32.const 35) (i32.const 0))
    (i32.store8 (i32.const 36) (i32.const 1))
    (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 3)
      (i32.const 28) (i32.const 9)))
)
