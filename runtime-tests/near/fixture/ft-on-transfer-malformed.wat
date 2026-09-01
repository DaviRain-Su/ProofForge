(module
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory (export "memory") 1)
  (data (i32.const 0) "\22\30\31\22")
  (func (export "ft_on_transfer") (call $value_return (i64.const 4) (i64.const 0))))
