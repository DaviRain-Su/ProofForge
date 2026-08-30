;; Local 2.6.1: after tfSendAmount funds the pseudo-account, can we write
;; ContractData under get_current_ledger_obj_field(sfContractAccount=524313)?
;; get_* ABI. Key "bal". Not Sdk.Map.
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
    (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 64) (i32.const 3)
      (i32.const 28) (i32.const 9)))

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "pokeCaller") (result i32)
    (local $st i32)
    (local.set $st (call $get_tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))

  (func (export "pokeSelf") (result i32)
    (local $st i32)
    (local.set $st (call $get_current_ledger_obj_field (i32.const 524313) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))
)
