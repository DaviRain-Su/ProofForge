;; Local 2.6.1-rc1: get_tx_field / get_current_ledger_obj_field.
;; sfContractAccount = 524315 on dangell/Bedrock (public 3.3.0 uses 524320).
;; Key "bal". UINT64 STI 3 big-endian value 1. Not Sdk.Map.
(module
  (import "host_lib" "get_tx_field"
    (func $get_tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "get_current_ledger_obj_field"
    (func $get_current_ledger_obj_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 64) "bal")

  (func $write_bal (result i32)
    (local $st i32)
    (i32.store8 (i32.const 28) (i32.const 3))
    (i32.store8 (i32.const 29) (i32.const 0))
    (i32.store8 (i32.const 30) (i32.const 0))
    (i32.store8 (i32.const 31) (i32.const 0))
    (i32.store8 (i32.const 32) (i32.const 0))
    (i32.store8 (i32.const 33) (i32.const 0))
    (i32.store8 (i32.const 34) (i32.const 0))
    (i32.store8 (i32.const 35) (i32.const 0))
    (i32.store8 (i32.const 36) (i32.const 1))
    (local.set $st (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 3)
      (i32.const 28) (i32.const 9)))
    (local.get $st))

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "pokeCaller") (result i32)
    (local $st i32)
    (local.set $st (call $get_tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))

  ;; 2.6.1 server_definitions: sfContractAccount = ACCOUNT/25 = 524313.
  (func (export "pokeSelf") (result i32)
    (local $st i32)
    (local.set $st (call $get_current_ledger_obj_field (i32.const 524313) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))

  ;; Contract SLE sfOwner = 524290 (Bedrock home field).
  (func (export "pokeOwner") (result i32)
    (local $st i32)
    (local.set $st (call $get_current_ledger_obj_field (i32.const 524290) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))
)
