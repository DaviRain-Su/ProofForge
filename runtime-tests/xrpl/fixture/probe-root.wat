;; Probe AccountRoot UInt32 fields via the already-green Balance host path.
;; accountroot_id + cache_le + le_field:
;;   Sequence   = 131076
;;   Flags      = 131074
;;   OwnerCount = 131085
;; Persist little-endian UInt32 as UINT64 JSON under the caller. Not Sdk.Account.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "accountroot_id"
    (func $accountroot_id (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "cache_le"
    (func $cache_le (param i32 i32 i32) (result i32)))
  (import "host_lib" "le_field"
    (func $le_field (param i32 i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 200) "seq")
  (data (i32.const 204) "flags")
  (data (i32.const 212) "ownc")

  ;; mem: 0..19 account, 32..63 index, 80..87 u32 scratch, 160..168 UINT64 store
  (func (export "initialize") (result i32)
    (i32.const 0))

  (func $store_u32 (param $key i32) (param $klen i32) (result i32)
    (local $st i32)
    ;; Host writes UInt32 little-endian at 80..83. Persist as UINT64 STI 3
    ;; + 8-byte big-endian (high 4 zeros, then bytes 83..80).
    (i32.store8 (i32.const 160) (i32.const 3))
    (i32.store8 (i32.const 161) (i32.const 0))
    (i32.store8 (i32.const 162) (i32.const 0))
    (i32.store8 (i32.const 163) (i32.const 0))
    (i32.store8 (i32.const 164) (i32.const 0))
    (i32.store8 (i32.const 165) (i32.load8_u (i32.const 83)))
    (i32.store8 (i32.const 166) (i32.load8_u (i32.const 82)))
    (i32.store8 (i32.const 167) (i32.load8_u (i32.const 81)))
    (i32.store8 (i32.const 168) (i32.load8_u (i32.const 80)))
    (local.set $st (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (local.get $key) (local.get $klen)
      (i32.const 160) (i32.const 9)))
    (local.get $st))

  (func (export "poke") (result i32)
    (local $st i32)
    (local $slot i32)
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $accountroot_id
      (i32.const 0) (i32.const 20) (i32.const 32) (i32.const 32)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $slot (call $cache_le (i32.const 32) (i32.const 32) (i32.const 0)))
    (if (i32.lt_s (local.get $slot) (i32.const 0))
      (then (return (local.get $slot))))

    (local.set $st (call $le_field
      (local.get $slot) (i32.const 131076) (i32.const 80) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $store_u32 (i32.const 200) (i32.const 3)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))

    (local.set $st (call $le_field
      (local.get $slot) (i32.const 131074) (i32.const 80) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $store_u32 (i32.const 204) (i32.const 5)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))

    (local.set $st (call $le_field
      (local.get $slot) (i32.const 131085) (i32.const 80) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $st (call $store_u32 (i32.const 212) (i32.const 4)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
