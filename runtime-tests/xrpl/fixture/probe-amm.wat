;; Probe AlphaNet host_lib AMM read path (XLS-0102 hosts, XLS-30 object). Not Sdk.Amm.
;; Path: amm_id(issue1, issue2, 32B out) -> cache_le(32B id) -> le_field.
;; Issue buffers are canonical 40-byte non-XRP STIssue serializations:
;; 20-byte currency (12 zero + 3 ASCII + 5 zero) + 20-byte issuer AccountID.
;; 20-byte non-XRP issues returned INVALID_PARAMS (-15), so per the XRPL
;; binary-format Issue rule (only XRP drops the issuer) we pass 40 bytes.
;; Issuer here is the probe master wallet b5f762798a53d543a014caf8b297cff8f2f937e8.
;; AMM sfields from the in-repo ripple-binary-codec definitions (AMM ledger
;; entry type 121): LPTokenBalance = Amount nth 31 = 393247.
;; Missing import -> ContractCreate fail. Object missing / bad params ->
;; negative vmReturnCode (e.g. -10 / -15), which means the path ran; codes
;; are reported as-is, not coerced to 0.
(module
  (import "host_lib" "amm_id"
    (func $amm_id (param i32 i32 i32 i32 i32 i32) (result i32)))
  (import "host_lib" "cache_le"
    (func $cache_le (param i32 i32 i32) (result i32)))
  (import "host_lib" "le_field"
    (func $le_field (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  ;; mem: issue1 0..39 (USD currency [12..14] + issuer), issue2 40..79
  ;; (EUR currency [52..54] + issuer), AMM id 96..127, le_field out 160..207
  (data (i32.const 12) "USD")
  (data (i32.const 32) "\b5\f7\62\79\8a\53\d5\43\a0\14\ca\f8\b2\97\cf\f8\f2\f9\37\e8")
  (data (i32.const 52) "EUR")
  (data (i32.const 60) "\b5\f7\62\79\8a\53\d5\43\a0\14\ca\f8\b2\97\cf\f8\f2\f9\37\e8")

  (func (export "initialize") (result i32)
    (i32.const 0))

  (func (export "poke") (result i32)
    (local $st i32)
    (local $slot i32)
    (local.set $st (call $amm_id
      (i32.const 0) (i32.const 40)
      (i32.const 40) (i32.const 40)
      (i32.const 96) (i32.const 32)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (local.set $slot (call $cache_le (i32.const 96) (i32.const 32) (i32.const 0)))
    (if (i32.lt_s (local.get $slot) (i32.const 0))
      (then (return (local.get $slot))))
    (local.set $st (call $le_field
      (local.get $slot) (i32.const 393247) (i32.const 160) (i32.const 48)))
    (if (i32.lt_s (local.get $st) (i32.const 0))
      (then (return (local.get $st))))
    (i32.const 0))
)