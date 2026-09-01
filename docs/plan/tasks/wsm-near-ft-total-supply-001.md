---
id: wsm-near-ft-total-supply-001
scope: wasm
status: done
depends-on: [wsm-near-json-u128-output-001, wsm-near-fungible-ledger-001]
---

# wsm-near-ft-total-supply-001 specialized total-supply view

## Objective

Expose the closed ledger's real lossless total supply through an exact `ft_total_supply` export and
canonical quoted-u128 output, without adding a second supply model or mutating FT JSON methods.

## Delivered

- `ft_total_supply` reads the integrated fixture state's ordered `supplyW0,supplyW1` leaves and
  selects the existing `near-json-u128-string-v1` output policy. It performs no balance-map
  operation, write, log, or Promise and calls `value_return` exactly once.
- Targeted and sandbox gates pin exact zero, mixed 2^64+1, and maximum-u128 wire bytes before and
  after real ledger mint/burn mutations. Existing `ft_balance_of` and `BAL2` scenes remain green.
- The original slice retained ProofForge's exact-zero-length request boundary. The later
  `wsm-near-no-args-input-001` slice explicitly opts this exact export into current near-sdk's
  generated no-args behavior, which does not read or validate request bytes.

## Authoritative compatibility boundary

Current near-sdk-rs code generation emits `env::input()` and JSON deserialization only when a
method has regular input arguments (`has_input_args`/`arg_parsing_tokens`). A zero-argument
`ft_total_supply` wrapper therefore ignores empty, `{}`, and arbitrary request bodies. ProofForge
now opts in only this annotated method; other zero-parameter methods retain exact-empty input.
The export and successful result bytes are official-shaped, but bounded argument policies elsewhere
still preclude a claim of full NEP-141/near-sdk ABI compatibility. No generic JSON, amount parser,
mutating FT method, resolver, registration enforcement, event coupling, or public contract is added.
