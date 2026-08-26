#!/usr/bin/env bash
# Run every EVM Anvil gate. Same script on Darwin and Linux.
# Missing Foundry → all cases skip (exit 0). Any fail-closed case → exit 1.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/evm/lib.sh
source "$here/lib.sh"

solana_lean_evm_init evm-anvil
echo "evm-anvil: host=$(uname -s)-$(uname -m) anvil=$anvil cast=$cast" >&2

failed=0
ran=0
skipped=0
for case in counter pair flag maybe ctx tipjar lang vault ownable token window phase wide; do
  script="$here/anvil_$case.sh"
  echo "evm-anvil: $case" >&2
  if out="$("$script" 2>&1)"; then
    echo "$out"
    if printf '%s\n' "$out" | grep -q ': skip:'; then
      skipped=$((skipped + 1))
    else
      ran=$((ran + 1))
    fi
  else
    echo "$out" >&2
    failed=$((failed + 1))
  fi
done

if [[ "$failed" -ne 0 ]]; then
  echo "evm-anvil: FAIL ($failed failed, $ran ok, $skipped skipped)" >&2
  exit 1
fi
echo "evm-anvil: ok ($ran ran, $skipped skipped; Darwin/Linux; engineering only)"
