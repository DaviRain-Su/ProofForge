;; Probe tx_field on the current ContractCall: Sequence (UInt32) and Fee (STAmount).
;; Sequence = 131076. Fee = 393224. Not Sdk.Log. Not a new host import.
(module
  (import "host_lib" "tx_field"
    (func $tx_field (param i32 i32 i32) (result i32)))
  (import "host_lib" "set_data_object_field"
    (func $set_data_object_field (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 200) "tseq")
  (data (i32.const 208) "tfee")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (local $st i32)
    ;; Owner = tx Account, so slot writes land on the caller.
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 0) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    ;; Sequence UInt32 LE at 80. Persist as UINT64 BE (high 4 zero, then bytes 83..80).
    (local.set $st (call $tx_field (i32.const 131076) (i32.const 80) (i32.const 8)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
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
      (i32.const 200) (i32.const 4)
      (i32.const 160) (i32.const 9)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    ;; Fee STAmount at 112. Persist first 8 bytes as UINT64 (host writes BE STAmount).
    (local.set $st (call $tx_field (i32.const 393224) (i32.const 112) (i32.const 48)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 160) (i32.const 3))
    (i32.store8 (i32.const 161) (i32.load8_u (i32.const 112)))
    (i32.store8 (i32.const 162) (i32.load8_u (i32.const 113)))
    (i32.store8 (i32.const 163) (i32.load8_u (i32.const 114)))
    (i32.store8 (i32.const 164) (i32.load8_u (i32.const 115)))
    (i32.store8 (i32.const 165) (i32.load8_u (i32.const 116)))
    (i32.store8 (i32.const 166) (i32.load8_u (i32.const 117)))
    (i32.store8 (i32.const 167) (i32.load8_u (i32.const 118)))
    (i32.store8 (i32.const 168) (i32.load8_u (i32.const 119)))
    (local.set $st (call $set_data_object_field
      (i32.const 0) (i32.const 20)
      (i32.const 208) (i32.const 4)
      (i32.const 160) (i32.const 9)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
