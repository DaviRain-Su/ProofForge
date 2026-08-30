# wsm-near-account-token-map-001 — specialized AccountId/NearToken Identity map

Status: done

Adds the closed `DirectAccountNearTokenMap` foundation. Its durable key is exactly a four-byte
compile-time namespace followed by canonical Borsh AccountId bytes (`u32_le(length) || active
UTF-8 bytes`), for a 10..72 byte key. Inactive carrier lanes never enter identity. Values are the
exact 16-byte little-endian Borsh representation of both `NearToken` limbs.

`read`, `has`, `put`, and `remove` preserve nearcore raw status. Reads fail closed unless the active
register is present, fits, and has length 16; zero remains a present value. Writes and removals are
immediate and write-last. The runtime fixture covers namespace separation, distinct self/caller
identities, short-key padding isolation, mixed/zero/max values, replacement, and reclamation.
Fixture-only malformed 8/20-byte seed entries prove that present-but-non-16-byte values fail closed
for both limbs and that a subsequent normal read cannot observe a stale register.

This is an internal specialized storage foundation, not a generic key/value API, FT ledger,
balance policy, event coupling, or NEP-141 public method ABI. Host context AccountIds are nominally
valid. The extractor rejects statically malformed carrier lengths outside 2..64; manually
constructed carriers are otherwise not syntax-validated by this map, and no dynamic public
AccountId decoder exists in this slice.
