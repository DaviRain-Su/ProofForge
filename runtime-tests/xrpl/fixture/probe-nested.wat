;; Probe set/get_data_nested_object_field. Not Sdk.Map.
;; Signature: (acc, acc_len, key, key_len, nested, nested_len, data, data_len) -> i32.
;; Missing import → ContractCreate fail.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_nested_object_field"
    (func $set_nested (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (import "host_lib" "get_data_nested_object_field"
    (func $get_nested (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 64) "user")
  (data (i32.const 68) "bal")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (local $st i32)
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 28) (i32.const 3))
    (i32.store8 (i32.const 29) (i32.const 0))
    (i32.store8 (i32.const 30) (i32.const 0))
    (i32.store8 (i32.const 31) (i32.const 0))
    (i32.store8 (i32.const 32) (i32.const 0))
    (i32.store8 (i32.const 33) (i32.const 0))
    (i32.store8 (i32.const 34) (i32.const 0))
    (i32.store8 (i32.const 35) (i32.const 0))
    (i32.store8 (i32.const 36) (i32.const 7))
    (local.set $st (call $set_nested
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 4)
      (i32.const 68) (i32.const 3)
      (i32.const 28) (i32.const 9)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
