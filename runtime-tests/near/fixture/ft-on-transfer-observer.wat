(module
  ;; Test-only child receiver. It returns `attached_deposit[16] || input` so the Promise sandbox can
  ;; observe the exact composed `ft_on_transfer` JSON and zero u128 deposit without claiming a
  ;; ProofForge JSON decoder or fungible-token receiver implementation.
  (import "env" "input" (func $input (param i64)))
  (import "env" "register_len" (func $register_len (param i64) (result i64)))
  (import "env" "read_register" (func $read_register (param i64 i64)))
  (import "env" "attached_deposit" (func $attached_deposit (param i64)))
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory (export "memory") 1)

  (func (export "ft_on_transfer")
    (local $len i64)
    (call $input (i64.const 0))
    (local.set $len (call $register_len (i64.const 0)))
    (call $attached_deposit (i64.const 0))
    (call $read_register (i64.const 0) (i64.const 16))
    (call $value_return (i64.add (i64.const 16) (local.get $len)) (i64.const 0)))
)
