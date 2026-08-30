;; Local 2.6.1-rc1: does ContractCall Parameters reach function_param?
;; Not XrplSmoke digest. Not public 3.3.0 HTTP 502 probe.
(module
  (import "host_lib" "function_param"
    (func $function_param (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  (func (export "initialize") (result i32)
    (i32.const 0))

  ;; Copies UINT64 parameter 0 into mem[20..27]. Positive = bytes written.
  (func (export "bump") (result i32)
    (call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8)))
)
