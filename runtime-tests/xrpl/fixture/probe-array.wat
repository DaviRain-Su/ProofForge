;; Probe set_data_array_element_field. 7-param import instantiates on this image.
;; Call order: account, key, index, value (key before index).
(module
  (import "host_lib" "get_current_ledger_obj_field"
    (func $get_current_ledger_obj_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_array_element_field"
    (func $set_data_array_element_field (param i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 64) "xs")
  (data (i32.const 80) "value")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (local $st i32)
    (local $arr i32)
    (local.set $st (call $get_current_ledger_obj_field
      (i32.const 524290) (i32.const 0) (i32.const 20)))
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
    ;; account, key, index, data
    (local.set $arr (call $set_data_array_element_field
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 2)
      (i32.const 0)
      (i32.const 28) (i32.const 9)))
    (i32.store8 (i32.const 28) (i32.const 3))
    (i32.store8 (i32.const 29) (i32.const 0))
    (i32.store8 (i32.const 30) (i32.const 0))
    (i32.store8 (i32.const 31) (i32.const 0))
    (i32.store8 (i32.const 32) (i32.const 0))
    (i32.store8 (i32.const 33) (i32.const 0))
    (i32.store8 (i32.const 34) (i32.const 0))
    (i32.store8 (i32.const 35) (i32.const 0))
    (i32.store8 (i32.const 36) (i32.and (local.get $arr) (i32.const 255)))
    (local.set $st (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 80) (i32.const 5)
      (i32.const 28) (i32.const 9)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
