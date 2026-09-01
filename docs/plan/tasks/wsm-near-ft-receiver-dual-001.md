---
id: wsm-near-ft-receiver-dual-001
scope: wasm
status: done
depends-on: [wsm-near-json-ft-on-transfer-input-001, wsm-near-promise-or-value-u128-001, wsm-near-ft-transfer-call-001]
---

# wsm-near-ft-receiver-dual-001 runtime Promise-or-value FT receiver

## Objective

Apply the compiler-owned Promise-or-quoted-U128 terminal to one exact `ft_on_transfer` business
boundary and verify both runtime alternatives through the integrated token/resolver chain.

## Delivered

- `NearFtReceiverDual.ft_on_transfer` is a non-payable exact export over the compiler-owned
  20-leaf `FtOnTransferArgs` frame. One invocation-time message-length branch returns a canonical
  quoted unused amount; another returns one static child Promise. Both persist an independent call
  count and message length before their unique terminal.
- Structural checks pin the exact input/output policies, three immediate and three Promise
  terminals, Promise creation/action/return support, and state stores before either terminal kind.
  Ordinary quoted-U128 methods remain unaffected by the explicit annotation. Canonical target-IR
  digest: `d03ecd932c8aebc0`.
- `ledger.sh` deploys the receiver onto an existing registered BAL2 recipient and drives the real
  token `ft_transfer_call → ft_on_transfer → ft_resolve_transfer` DAG. Immediate full/zero/partial
  unused values and returned valid/failed/malformed results produce exact outer used amounts,
  transfer/refund events, balances, present-zero registration, and conserved supply. Receiver state
  persists before asynchronous child outcomes; non-payable and malformed-input failures roll back.
  A source `Except.error` receipt also leaves receiver state unchanged and drives the resolver's
  exact full-refund path.

## Boundary

The Promise-or-value output and receipt semantics match this NEP-141 receiver boundary, but input
remains ProofForge's 1071-byte bounded canonical JSON subset rather than near-sdk's complete serde
language. The receiver's message-length policy and static result child are diagnostic business
logic, not a reusable token-receiver policy or a complete NEP-141 compatibility claim.
