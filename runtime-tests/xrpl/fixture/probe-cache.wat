;; Probe host_lib.cache_le (XLS-0102 / stdlib rename of cache_ledger_obj).
;; Signature: (id_ptr i32, id_len i32, cache_num i32) -> i32.
;; This module only instantiates and calls with a 32-byte zero id and cache_num 0.
;; Negative host code is success-of-probe (host exists). Missing import → ContractCreate fail.
(module
  (import "host_lib" "cache_le"
    (func $cache_le (param i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    ;; 32 zero bytes at 0; cache_num 0. Host may return slot or negative error.
    ;; We return the host code as i32 status so the gate can print it.
    (call $cache_le (i32.const 0) (i32.const 32) (i32.const 0)))
)
