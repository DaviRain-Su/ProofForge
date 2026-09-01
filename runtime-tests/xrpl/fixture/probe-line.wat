;; Probe AlphaNet trustline_id (XLS-0102). Fallback name is Transia line_keylet.
;; Eight i32s: acc1, len, acc2, len, currency, len, out, out_len.
;; Missing import → ContractCreate fail. Any poke i32 = host exists.
(module
  (import "host_lib" "trustline_id"
    (func $trustline_id (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (call $trustline_id
      (i32.const 0) (i32.const 20)
      (i32.const 20) (i32.const 20)
      (i32.const 40) (i32.const 20)
      (i32.const 64) (i32.const 32)))
)
