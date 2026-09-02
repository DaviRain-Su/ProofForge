#!/usr/bin/env bash
# Local CI mirror for ProofForge.
#
# Run the same gates a PR would hit *before* pushing to GitHub.
# Default mode auto-selects lanes from paths changed against the merge base
# (origin/main), matching .github/workflows/ci.yml path filters.
#
# Usage:
#   scripts/ci_local.sh                  # auto lanes from git diff
#   scripts/ci_local.sh --lane lean
#   scripts/ci_local.sh --lane svm --lane near
#   scripts/ci_local.sh --all             # every lane + phoenix heavy
#   scripts/ci_local.sh --phoenix         # phoenix Mollusk + Surfpool only
#   scripts/ci_local.sh --fast            # python guards only
#   scripts/ci_local.sh --base origin/main
#   scripts/ci_local.sh --surfpool-heavy  # force Phoenix Mollusk + Surfpool on svm
#
# Env:
#   CI_LOCAL_BASE   override merge-base ref
#   SKIP_SETUP=1    skip .agents/setup
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASE="${CI_LOCAL_BASE:-origin/main}"
FAST=0
ALL=0
PHOENIX=0
SURFPOOL_HEAVY=0
declare -a LANES=()

usage() {
  sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage 0 ;;
    --base) BASE="$2"; shift 2 ;;
    --lane) LANES+=("$2"); shift 2 ;;
    --all) ALL=1; shift ;;
    --phoenix) PHOENIX=1; shift ;;
    --fast) FAST=1; shift ;;
    --surfpool-heavy) SURFPOOL_HEAVY=1; shift ;;
    *) echo "unknown arg: $1" >&2; usage 1 ;;
  esac
done

log() { printf '\n==> %s\n' "$*"; }

have_lane() {
  local want="$1" lane
  for lane in "${LANES[@]+"${LANES[@]}"}"; do
    [[ "$lane" == "$want" ]] && return 0
  done
  return 1
}

# Prefix match: pattern may end with /** meaning directory tree.
matches_any() {
  local file="$1"; shift
  local pat
  for pat in "$@"; do
    if [[ "$pat" == */** ]]; then
      local prefix="${pat/%\/**/}"
      [[ "$file" == "$prefix" || "$file" == "$prefix"/* ]] && return 0
    else
      [[ "$file" == "$pat" ]] && return 0
    fi
  done
  return 1
}

detect_lanes() {
  git rev-parse --verify "$BASE" >/dev/null 2>&1 || git fetch origin main 2>/dev/null || true
  local mb
  if ! mb="$(git merge-base HEAD "$BASE" 2>/dev/null)"; then
    mb="$(git rev-parse HEAD)"
  fi
  mapfile -t CHANGED < <({
    git diff --name-only "$mb" HEAD
    git diff --name-only --cached
    git diff --name-only
  } | awk 'NF && !seen[$0]++')

  if ((${#CHANGED[@]} == 0)); then
    log "no changed files vs $BASE — defaulting to lean+svm (smoke)"
    LANES=(lean svm)
    SURFPOOL_HEAVY=0
    return
  fi
  printf 'changed files (merge-base %s):\n' "$mb" >&2
  printf '  %s\n' "${CHANGED[@]}" >&2

  local lean=0 svm=0 evm=0 near=0 shared=0 heavy=0 f
  for f in "${CHANGED[@]}"; do
    matches_any "$f" \
      '.github/workflows/ci.yml' '.agents/setup' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      'ProofForge/Cli.lean' 'ProofForge/Attr.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' \
      'ProofForge/Core/**' 'ProofForge/Crypto/**' 'ProofForge/Profile.lean' \
      && shared=1
    matches_any "$f" \
      'ProofForge/**' 'Tests/**' 'Tests.lean' 'Examples/**' 'Examples.lean' \
      'scripts/check_ownership.py' 'scripts/check_no_sorry.py' 'scripts/check_artifact_manifest.py' \
      'scripts/check_sdk_import_closure.py' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      '.github/workflows/ci.yml' '.agents/setup' \
      && lean=1
    matches_any "$f" \
      'ProofForge/Svm/**' 'Examples/Svm/**' 'runtime-tests/solana/**' 'runtime-tests/surfpool/**' \
      'scripts/check_ownership.py' 'scripts/check_no_sorry.py' 'scripts/check_artifact_manifest.py' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' \
      && svm=1
    matches_any "$f" \
      'ProofForge/Evm/**' 'ProofForge/Wasm/**' 'Examples/Evm/**' 'Examples/Xrpl/**' \
      'runtime-tests/evm/**' 'runtime-tests/xrpl/**' 'scripts/check_artifact_manifest.py' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' \
      && evm=1
    matches_any "$f" \
      'ProofForge/Wasm/**' 'Examples/Near/**' 'runtime-tests/near/**' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' \
      && near=1
    matches_any "$f" \
      'Examples/Svm/Phoenix.lean' 'Examples/Svm/PhoenixV1Layout.lean' 'Examples/Svm/PhoenixV1Profile.lean' \
      'ProofForge/Svm/AccountStorage/**' 'ProofForge/Svm/FifoCancel/**' 'ProofForge/Svm/Emit.lean' \
      'runtime-tests/solana/tests/phoenix.rs' 'runtime-tests/solana/tests/phoenix_v1_profile.rs' \
      'runtime-tests/surfpool/**' '.github/workflows/ci-phoenix.yml' '.agents/setup' \
      && heavy=1
  done

  if (( shared )); then lean=1; svm=1; evm=1; near=1; heavy=1; fi
  LANES=()
  (( lean )) && LANES+=(lean)
  (( svm )) && LANES+=(svm)
  (( evm )) && LANES+=(evm)
  (( near )) && LANES+=(near)
  if (( heavy )); then SURFPOOL_HEAVY=1; fi
  if ((${#LANES[@]} == 0)); then
    log "docs/website/unrelated paths only — running --fast guards"
    FAST=1
    LANES=(guards)
  fi
}

if (( FAST )); then
  # --fast is guards-only; do not auto-expand into lake/cargo lanes.
  LANES=(guards)
  SURFPOOL_HEAVY=0
elif (( ALL )); then
  LANES=(lean svm evm near)
  SURFPOOL_HEAVY=1
  PHOENIX=1
elif (( PHOENIX )) && ((${#LANES[@]} == 0)); then
  LANES=(phoenix)
  SURFPOOL_HEAVY=1
elif ((${#LANES[@]} == 0)); then
  detect_lanes
fi

log "lanes: ${LANES[*]-none}  surfpool_heavy=${SURFPOOL_HEAVY}  fast=${FAST}"

if [[ "${SKIP_SETUP:-0}" != "1" && "$FAST" != "1" ]]; then
  if [[ -x .agents/setup ]]; then
    log "Prepare pinned toolchains (.agents/setup)"
    ./.agents/setup
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.foundry/bin:$HOME/.elan/bin:${PATH:-}"
  fi
fi

run_guards() {
  log "Python ownership / SDK / manifest / no-sorry guards"
  python3 scripts/check_ownership.py
  python3 scripts/check_sdk_import_closure.py
  python3 scripts/check_artifact_manifest.py --self-test
  python3 scripts/check_no_sorry.py
}

run_lean() {
  run_guards
  log "lake build"
  lake build
  log "formalization gate modules"
  lake build ProofForgeSvmSdk ProofForgeEvmSdk
  lake build Tests.ProofSpec Tests.SolanalibSpec Tests.SemanticsSpec
  log "lake build Tests"
  lake build Tests
}

run_svm() {
  local out="${PF_OUT_SVM:-build/sbpf}"
  log "lake build Examples"
  lake build Examples
  log "pf build --target svm"
  lake exe pf -- build --target svm --out "$out"
  python3 scripts/check_artifact_manifest.py --target svm --out "$out"
  if (( SURFPOOL_HEAVY || PHOENIX )); then
    log "Mollusk (including Phoenix)"
    cargo test --locked --manifest-path runtime-tests/solana/Cargo.toml -- --test-threads=1
    log "Surfpool Phoenix + PhoenixV1Profile + RawEntry"
    runtime-tests/surfpool/smoke.sh Phoenix
    runtime-tests/surfpool/smoke.sh PhoenixV1Profile
    runtime-tests/surfpool/smoke.sh RawEntry
  else
    log "Mollusk (without Phoenix; pass --surfpool-heavy to enable)"
    cargo test --locked --manifest-path runtime-tests/solana/Cargo.toml --no-default-features -- --test-threads=1
    log "Surfpool RawEntry only"
    runtime-tests/surfpool/smoke.sh RawEntry
  fi
}

run_evm() {
  local out="${PF_OUT_EVM:-build/evm}"
  log "lake build Examples"
  lake build Examples
  log "pf build --target evm + xrpl"
  lake exe pf -- build --target evm --out "$out"
  python3 scripts/check_artifact_manifest.py --target evm --out "$out"
  lake exe pf -- build --target xrpl --out build/xrpl
  log "XRPL + Anvil gates (same scripts as ci.yml)"
  runtime-tests/xrpl/check.sh
  runtime-tests/xrpl/counter.sh
  runtime-tests/xrpl/ctx.sh
  runtime-tests/xrpl/own.sh
  runtime-tests/xrpl/hash.sh
  runtime-tests/xrpl/rt2.sh
  runtime-tests/xrpl/vec.sh
  runtime-tests/evm/anvil.sh
}

run_near() {
  local out="${PF_OUT_NEAR:-build/near}"
  # Match ci.yml after P0: Examples only — Lean lane owns Tests.
  log "lake build Examples (NEAR lane; no lake build Tests)"
  lake build Examples
  log "pf build --target near"
  lake exe pf -- build --target near --out "$out"
  log "NEAR wasm + sandbox gates (same scripts as ci.yml)"
  local scripts=(
    check counter context bytes ft_event token_arithmetic token_storage memory output
    storage_balance_output storage_balance_bounds_output
    json_account_input json_amount_input json_memo_input json_message_input
    json_ft_transfer_input json_ft_transfer_call_input json_ft_on_transfer_input
    ft_receiver_value promise_or_value json_ft_resolve_input
    json_storage_deposit_input json_storage_unregister_input json_storage_withdraw_input
    json_boolean_mutation storage storage_economics storage_registration
    vector lookup ledger queue iterable promise
  )
  local s
  for s in "${scripts[@]}"; do
    log "NEAR ${s}"
    "runtime-tests/near/${s}.sh"
  done
}

run_phoenix() {
  log "Phoenix heavy local gate (ci-phoenix.yml)"
  lake build Examples
  lake exe pf -- build --target svm --out "${PF_OUT_SVM:-build/sbpf}" Phoenix
  lake exe pf -- build --target svm --out "${PF_OUT_SVM:-build/sbpf}" PhoenixV1Profile
  cargo test --locked --manifest-path runtime-tests/solana/Cargo.toml -- --test-threads=1 phoenix
  runtime-tests/surfpool/smoke.sh Phoenix
  runtime-tests/surfpool/smoke.sh PhoenixV1Profile
  runtime-tests/surfpool/smoke.sh RawEntry
}

if (( FAST )) || have_lane guards; then
  run_guards
fi

have_lane lean && run_lean
have_lane svm && run_svm
have_lane evm && run_evm
have_lane near && run_near
have_lane phoenix && run_phoenix
if (( PHOENIX )) && ! have_lane phoenix && ! have_lane svm; then
  run_phoenix
fi

log "ci_local: OK (lanes: ${LANES[*]-none})"
