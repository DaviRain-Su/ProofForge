;; Probe AlphaNet host_lib transaction emission (Transia / dangell smart-contracts).
;; Not XLS-0101 narrative `submitTransaction`. Not Sdk.Payments.
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

  ;; Host-exists probe. Payment type 0. Negative = host error, not missing import.
  (func (export "pokeBuild") (result i32)
    (call $build_txn (i32.const 0)))

  ;; 192 drops to the ContractCall Account. Contract must already hold XRP.
  ;; mem: 0 = 0x14, 1..20 = AccountID, 32..39 = STAmount.
  (func (export "pokeEmit") (result i32)
    (local $st i32)
    (local $idx i32)
    (local.set $st (call $tx_field (i32.const 524289) (i32.const 1) (i32.const 20)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.store8 (i32.const 0) (i32.const 0x14))
    ;; 0x40000000000000C0 = positive XRP | 192 drops, big-endian.
    (i32.store8 (i32.const 32) (i32.const 0x40))
    (i32.store8 (i32.const 33) (i32.const 0x00))
    (i32.store8 (i32.const 34) (i32.const 0x00))
    (i32.store8 (i32.const 35) (i32.const 0x00))
    (i32.store8 (i32.const 36) (i32.const 0x00))
    (i32.store8 (i32.const 37) (i32.const 0x00))
    (i32.store8 (i32.const 38) (i32.const 0x00))
    (i32.store8 (i32.const 39) (i32.const 0xC0))
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
    ;; Public 3.3.0 / 21337 = 0x00005359.
    (i32.store8 (i32.const 40) (i32.const 0x00))
    (i32.store8 (i32.const 41) (i32.const 0x00))
    (i32.store8 (i32.const 42) (i32.const 0x53))
    (i32.store8 (i32.const 43) (i32.const 0x59))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 131073) (i32.const 40) (i32.const 4)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    ;; sfFlags=131074. tfInnerBatchTxn = 0x40000000. Without it, 3.3.0
    ;; preclaim treats the inner Payment as a signed pseudo-account tx
    ;; and returns tefBAD_AUTH (-196).
    (i32.store8 (i32.const 44) (i32.const 0x40))
    (i32.store8 (i32.const 45) (i32.const 0x00))
    (i32.store8 (i32.const 46) (i32.const 0x00))
    (i32.store8 (i32.const 47) (i32.const 0x00))
    (local.set $st (call $add_txn_field
      (local.get $idx) (i32.const 131074) (i32.const 44) (i32.const 4)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (call $emit_built_txn (local.get $idx)))
)
