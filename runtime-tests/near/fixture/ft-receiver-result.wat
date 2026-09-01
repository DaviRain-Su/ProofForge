(module
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory (export "memory") 1)
  (data (i32.const 0) "\22\33\22\33")
  (func (export "unusedThree")
    (call $value_return (i64.const 3) (i64.const 0)))
  (func (export "malformed")
    (call $value_return (i64.const 1) (i64.const 3)))
  (func (export "failed") unreachable))
