;; Probe: can set_data_object_field write ContractData under the contract
;; account (sfContractAccount) rather than the tx Account (caller)?
;; AlphaNet XLS-0102 names. Key "bal". UINT64 STI 3 big-endian value 1.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "home_le_field"
    (func $home_le_field (param i32 i32 i32) (result i32)))
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

  ;; Write bal=1 under tx Account (current AlphaNet default).
  (func (export "pokeCaller") (result i32)
    (local $st i32)
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))

  ;; Write bal=1 under sfContractAccount (the contract SLE).
  (func (export "pokeSelf") (result i32)
    (local $st i32)
    (local.set $st (call $home_le_field (i32.const 524320) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $write_bal))
)
