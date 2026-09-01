;; Local transia/alphanet 2.6.1-rc1 (dangell/smart-contracts) host names.
;; Not public 3.3.0-rc1 XLS-0102 (`tx_field`). Not Sdk.Payments.
;;
;;   build_txn / add_txn_field / emit_built_txn  — same on both nodes
;;   get_tx_field                               — this node; public uses tx_field
;;
;; Payment = 0. Amount = 393217. Destination = 524291.
(module
  (import "host_lib" "build_txn"
    (func $build_txn (param i32) (result i32)))
  (import "host_lib" "add_txn_field"
    (func $add_txn_field (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "emit_built_txn"
    (func $emit_built_txn (param i32) (result i32)))
  (import "host_lib" "get_tx_field"
    (func $get_tx_field (param i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "pokeBuild") (result i32)
    (call $build_txn (i32.const 0)))

  (func (export "pokeEmit") (result i32)
    (local $st i32)
    (local $idx i32)
    (local.set $st (call $get_tx_field (i32.const 524289) (i32.const 1) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 0) (i32.const 0x14))
    (i32.store8 (i32.const 32) (i32.const 0x40))
    (i32.store8 (i32.const 33) (i32.const 0x00))
    (i32.store8 (i32.const 34) (i32.const 0x00))
    (i32.store8 (i32.const 35) (i32.const 0x00))
    (i32.store8 (i32.const 36) (i32.const 0x00))
    (i32.store8 (i32.const 37) (i32.const 0x00))
    (i32.store8 (i32.const 38) (i32.const 0x00))
    (i32.store8 (i32.const 39) (i32.const 0xC0))
    ;; sfNetworkID = 131073. Host get_tx_field writes UInt32 little-endian;
    ;; add_txn_field wants ST UInt32 big-endian. 63456 = 0x0000F7E0.
    (i32.store8 (i32.const 40) (i32.const 0x00))
    (i32.store8 (i32.const 41) (i32.const 0x00))
    (i32.store8 (i32.const 42) (i32.const 0xF7))
    (i32.store8 (i32.const 43) (i32.const 0xE0))
    (local.set $idx (call $build_txn (i32.const 0)))
    (if (i32.lt_s (local.get $idx) (i32.const 0))
      (then (return (local.get $idx))))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 393217) (i32.const 32) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 524291) (i32.const 0) (i32.const 21)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 131073) (i32.const 40) (i32.const 4)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $emit_built_txn (local.get $idx)))
)
