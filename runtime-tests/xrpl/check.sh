#!/usr/bin/env bash
# XRPL Bedrock engineering gate (WASM family): emit every registered xrpl program,
# then type-check each generated Rust source against the local xrpl_wasm_std stub.
# This gate makes NO claim about bedrock / rippled / ContractCreate / AlphaNet /
# mainnet; the stub is not the real crate.
set -euo pipefail
cd "$(dirname "$0")/../.."

OUT=${OUT:-build/xrpl}
lake exe pf -- build --target xrpl --out "$OUT"

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp -r runtime-tests/xrpl/xrpl_wasm_std_stub "$TMP/xrpl_wasm_std"
mkdir -p "$TMP/check/src"
cat > "$TMP/check/Cargo.toml" <<'TOML'
[package]
name = "pf_wasm_check"
version = "0.0.0"
edition = "2021"
[lib]
crate-type = ["cdylib"]
[dependencies]
xrpl_wasm_std = { path = "../xrpl_wasm_std" }
TOML

shopt -s nullglob
for rs in "$OUT"/*.rs; do
  cp "$rs" "$TMP/check/src/lib.rs"
  (cd "$TMP/check" && cargo check --offline -q)
  # every registered program must export at least one Bedrock entry
  grep -q 'pub extern "C" fn' "$rs"
  echo "xrpl check ok: $(basename "$rs")"
done
echo "xrpl engineering gate: ok"