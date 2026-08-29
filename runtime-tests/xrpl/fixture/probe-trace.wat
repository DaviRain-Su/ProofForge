;; Probe host_lib.trace_num (XLS-0102 §5.9). Debug log only, not EVM LOG.
;; Signature: (msg_ptr i32, msg_len i32, number i64) -> i32. 0 success, negative error.
(module
  (import "host_lib" "trace_num"
    (func $trace_num (param i32 i32 i64) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 64) "n")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (local $st i32)
    (local.set $st (call $trace_num (i32.const 64) (i32.const 1) (i64.const 7)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)
