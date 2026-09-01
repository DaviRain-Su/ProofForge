;; Probe AlphaNet host_lib transaction emission.
;; Official emit_txn fixture: Amount + Destination only. Not Sdk.Payments.
;;
;;   build_txn(tt) -> i32
;;   add_txn_field(index, sfield, ptr, len) -> i32
;;   emit_built_txn(index) -> i32
;;
;; Payment = 0. Amount = 393217 (8-byte XRP STAmount). Destination = 524291
;; (0x14 || 20-byte AccountID). pokeBuild only instantiates the builder.
;; pokeEmit pays 192 drops from the contract pseudo-account to the caller.
(module
  (import "host_lib" "build_txn"
    (func $build_txn (param i32) (result i32)))
  (import "host_lib" "add_txn_field"
    (func $add_txn_field (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "emit_built_txn"
    (func $emit_built_txn (param i32) (result i32)))
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "pokeBuild") (result i32)
    (call $build_txn (i32.const 0)))

  ;; mem: 64 = 0x14, 65..84 = AccountID; 96..103 = STAmount.
  (func (export "pokeEmit") (result i32)
    (local $st i32)
    (local $idx i32)
    (i32.store8 (i32.const 64) (i32.const 0x14))
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 65) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    ;; 0x40000000000000C0 = positive XRP | 192 drops, big-endian.
    (i32.store8 (i32.const 96) (i32.const 0x40))
    (i32.store8 (i32.const 97) (i32.const 0x00))
    (i32.store8 (i32.const 98) (i32.const 0x00))
    (i32.store8 (i32.const 99) (i32.const 0x00))
    (i32.store8 (i32.const 100) (i32.const 0x00))
    (i32.store8 (i32.const 101) (i32.const 0x00))
    (i32.store8 (i32.const 102) (i32.const 0x00))
    (i32.store8 (i32.const 103) (i32.const 0xC0))
    (local.set $idx (call $build_txn (i32.const 0)))
    (if (i32.lt_s (local.get $idx) (i32.const 0))
      (then (return (local.get $idx))))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 393217) (i32.const 96) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 524291) (i32.const 64) (i32.const 21)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $emit_built_txn (local.get $idx)))
)
