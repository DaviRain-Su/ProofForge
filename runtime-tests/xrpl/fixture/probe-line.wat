;; Probe AlphaNet RippleState read path (XLS-0102). Not Sdk.Trustline.
;; caller = tx_field(sfAccount); issuer = compile-time 20B; currency = ISO USD.
;; trustline_id → cache_le → le_field(Balance=393218).
;; On success persists the first 8 Balance STAmount bytes as UINT64 key
;; "drops" (same layout as probe-balance.wat). A missing SLE still returns
;; the negative host code (-10 is not balance 0). Missing import →
;; ContractCreate fail.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "trustline_id"
    (func $trustline_id (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (import "host_lib" "cache_le"
    (func $cache_le (param i32 i32 i32) (result i32)))
  (import "host_lib" "le_field"
    (func $le_field (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  ;; issuer wallet B: d0bc2a540b15411f44a24dfb58d23ad5d9d9b350
  (data (i32.const 20) "\d0\bc\2a\54\0b\15\41\1f\44\a2\4d\fb\58\d2\3a\d5\d9\d9\b3\50")
  ;; ISO USD at currency[12..14]; 20-byte buffer at 40 is otherwise zero.
  (data (i32.const 52) "USD")
  (data (i32.const 200) "drops")

  (func (export "initialize") (result i32)
    (i32.const 0))

  ;; mem: 96..143 Balance STAmount, 160..168 UINT64 store, 200 "drops"
  (func (export "poke") (result i32)
    (local $st i32)
    (local $slot i32)
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $trustline_id
      (i32.const 0) (i32.const 20)
      (i32.const 20) (i32.const 20)
      (i32.const 40) (i32.const 20)
      (i32.const 64) (i32.const 32)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $slot (call $cache_le (i32.const 64) (i32.const 32) (i32.const 0)))
    (if (i32.lt_s (local.get $slot) (i32.const 0))
      (then (return (local.get $slot))))
    (local.set $st (call $le_field
      (local.get $slot) (i32.const 393218) (i32.const 96) (i32.const 48)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 160) (i32.const 3))
    (i32.store8 (i32.const 161) (i32.load8_u (i32.const 96)))
    (i32.store8 (i32.const 162) (i32.load8_u (i32.const 97)))
    (i32.store8 (i32.const 163) (i32.load8_u (i32.const 98)))
    (i32.store8 (i32.const 164) (i32.load8_u (i32.const 99)))
    (i32.store8 (i32.const 165) (i32.load8_u (i32.const 100)))
    (i32.store8 (i32.const 166) (i32.load8_u (i32.const 101)))
    (i32.store8 (i32.const 167) (i32.load8_u (i32.const 102)))
    (i32.store8 (i32.const 168) (i32.load8_u (i32.const 103)))
    (local.set $st (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 200) (i32.const 5)
      (i32.const 160) (i32.const 9)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
