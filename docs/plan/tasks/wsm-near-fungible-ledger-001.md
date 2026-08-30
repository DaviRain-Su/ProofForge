# wsm-near-fungible-ledger-001 — closed internal FT ledger foundation

Status: done

Adds a closed fixture-backed fungible-ledger policy over `DirectAccountNearTokenMap`, checked
two-limb `NearToken` arithmetic, and two ordinary state limbs for total supply. The reusable SDK
boundary owns active-snapshot validity/zero interpretation; the fixture owns policy. Missing
balances decode as zero. Present values must be an exact fitting 16-byte little-endian u128;
malformed values reject
before arithmetic or mutation. Zero amounts validate the relevant snapshots and then perform no
balance or supply mutation (the ordinary mutating wrapper may persist an unchanged state leaf).

Mint validates balance and supply additions before writing the balance; its returned state commits
supply last. Burn validates balance and supply subtraction before writing and removes a zero result.
Transfer snapshots both source limbs before the destination read, validates both sides before its
first balance write, removes a zero source, and leaves supply unchanged. Equal source/destination
validates the source and sufficiency, then performs no ledger mutation. Distinct transfer writes source then destination;
all business failures precede both, while NEAR receipt rollback remains the safety net for a later
host/state trap.

The sandbox fixture covers missing and malformed balances, zero amounts, low/high/mixed/max u128,
balance/destination/supply overflow, balance/supply underflow, alias and distinct transfer,
reclamation, rejected-receipt state preservation, and fixture-scene conservation. Dedicated
inconsistent-state seeds exist only to reach arithmetic failures that conservation makes
unreachable.

This is not a public NEP-141 contract. It has no JSON method ABI, registration/storage-management
policy, attached-deposit checks, resolver, event coupling, or externally parameterized ledger API.
Unlike near-sdk-rs, missing accounts are treated as zero and amount-zero operations are accepted as
validated no-ops; near-sdk-rs internal transfer rejects self-transfer and zero. The fixture's single
v0 error channel traps with the existing `overflow` panic for every closed rejection category.
