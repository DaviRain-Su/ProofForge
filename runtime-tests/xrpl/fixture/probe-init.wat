;; First-install Function ABI + initialize UINT64. Unique hash.
;; Writes param 0 into slot "value". Not Counter digest. AlphaNet XLS-0102.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "function_param"
    (func $function_param (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 64) "value")

  (func (export "initialize") (result i32)
    (local $st i32)
    (local $v i64)
    (local.set $st (call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $v (i64.load (i32.const 20)))
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 28) (i32.const 3))
    (i32.store8 (i32.const 29) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 56))))
    (i32.store8 (i32.const 30) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 48))))
    (i32.store8 (i32.const 31) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 40))))
    (i32.store8 (i32.const 32) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 32))))
    (i32.store8 (i32.const 33) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 24))))
    (i32.store8 (i32.const 34) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 16))))
    (i32.store8 (i32.const 35) (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 8))))
    (i32.store8 (i32.const 36) (i32.wrap_i64 (local.get $v)))
    (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 5)
      (i32.const 28) (i32.const 9)))
)
