---
id: wsm-near-ft-metadata-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-metadata-output-001, wsm-near-no-args-input-001]
---

# wsm-near-ft-metadata-001 bounded public-shaped metadata view

## Objective

Compose the bounded metadata serializer with the current near-sdk no-argument request-ignore
wrapper under the exact `ft_metadata` export, without widening the codec or misrepresenting the
optional near-contract-standards validator.

## Delivered

- Exact view export `ft_metadata` ignores arbitrary request bytes and returns one fixed configured
  object with `spec = "ft-1.0.0"`, matching reference/hash presence, and the exact SHA-256 of its
  reference URI.
- The configured value therefore satisfies near-contract-standards `assert_valid` by construction.
  The serializer itself remains a codec: it does not automatically run `assert_valid`, and the
  diagnostic carriers that exercise mismatched reference/hash presence remain valid codec tests.
- Structural and real-nearcore tests pin the exact export name, request-ignore policy, field bytes,
  one 2929-byte arena, one `value_return`, and absence of state writes, logs, or Promise effects.

## Compatibility boundary

Name/symbol/icon/reference capacities 64/16/256/128 are ProofForge product limits; the standard
does not impose them. The exact method name and configured valid value therefore do not claim a
fully general NEP-148 ABI.
