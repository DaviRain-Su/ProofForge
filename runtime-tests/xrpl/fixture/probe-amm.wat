;; Probe AlphaNet XLS-0102 amm_id import. Not Sdk.Amm.
;; Signature: (issue1_ptr, issue1_len, issue2_ptr, issue2_len, out_ptr, out_len) -> i32.
;; Dummy 20-byte zero issues. Missing import → ContractCreate fail.
;; Any wasm i32 from poke means the host exists.
(module
  (import "host_lib" "amm_id"
    (func $amm_id (param i32 i32 i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (call $amm_id
      (i32.const 0) (i32.const 20)
      (i32.const 20) (i32.const 20)
      (i32.const 64) (i32.const 32)))
)
