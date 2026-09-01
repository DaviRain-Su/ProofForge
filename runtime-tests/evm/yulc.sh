#!/usr/bin/env bash
# Feature B yulc gates: compile smoke + optional Anvil dual-backend.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cd "$root"

failed=0
run_gate() {
  local label="$1" path="$2"
  echo "evm-yulc: $label" >&2
  if out="$("$path" 2>&1)"; then
    echo "$out"
  else
    echo "$out" >&2
    failed=$((failed + 1))
  fi
}

run_gate smoke "./scripts/smoke_yulc_counter.sh"
run_gate anvil-counter "$here/anvil_yulc_counter.sh"
run_gate anvil-capped "$here/anvil_yulc_capped.sh"
run_gate anvil-const "$here/anvil_yulc_const.sh"
run_gate anvil-flag "$here/anvil_yulc_flag.sh"
run_gate anvil-phase "$here/anvil_yulc_phase.sh"

if [[ "$failed" -ne 0 ]]; then
  echo "evm-yulc: FAIL ($failed failed)" >&2
  exit 1
fi
echo "evm-yulc: ok"
