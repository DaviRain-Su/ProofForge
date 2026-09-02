#!/usr/bin/env bash
# Local CI mirror for ProofForge — run the same lane gates *before* pushing.
#
# Usage:
#   scripts/ci_local.sh                  # auto lanes from git diff vs origin/main
#   scripts/ci_local.sh --fast           # python guards only
#   scripts/ci_local.sh --lane lean
#   scripts/ci_local.sh --lane svm --lane near
#   scripts/ci_local.sh --phoenix        # dedicated Phoenix lane
#   scripts/ci_local.sh --all            # every lane including Phoenix
#   scripts/ci_local.sh --base origin/main
#
# Env: CI_LOCAL_BASE, SKIP_SETUP=1
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASE="${CI_LOCAL_BASE:-origin/main}"
FAST=0
ALL=0
PHOENIX_ONLY=0
declare -a LANES=()

usage() { sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage 0 ;;
    --base) BASE="$2"; shift 2 ;;
    --lane) LANES+=("$2"); shift 2 ;;
    --all) ALL=1; shift ;;
    --phoenix) PHOENIX_ONLY=1; shift ;;
    --fast) FAST=1; shift ;;
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
  mb="$(git merge-base HEAD "$BASE" 2>/dev/null || git rev-parse HEAD)"
  mapfile -t CHANGED < <({
    git diff --name-only "$mb" HEAD
    git diff --name-only --cached
    git diff --name-only
  } | awk 'NF && !seen[$0]++')

  if ((${#CHANGED[@]} == 0)); then
    log "no changed files vs $BASE — defaulting to lean+svm"
    LANES=(lean svm)
    return
  fi
  printf 'changed files (merge-base %s):\n' "$mb" >&2
  printf '  %s\n' "${CHANGED[@]}" >&2

  local lean=0 svm=0 evm=0 near=0 phoenix=0 shared=0 f
  for f in "${CHANGED[@]}"; do
    matches_any "$f" \
      '.github/workflows/ci.yml' '.agents/setup' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      'ProofForge/Cli.lean' 'ProofForge/Attr.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' \
      'ProofForge/Core/**' 'ProofForge/Crypto/**' 'ProofForge/Profile.lean' && shared=1
    matches_any "$f" \
      'ProofForge/**' 'Tests/**' 'Tests.lean' 'Examples/**' 'Examples.lean' \
      'scripts/check_*.py' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      '.github/workflows/ci.yml' '.agents/setup' && lean=1
    matches_any "$f" \
      'ProofForge/Svm/**' 'Examples/Svm/**' 'runtime-tests/solana/**' 'runtime-tests/surfpool/**' \
      'scripts/check_ownership.py' 'scripts/check_no_sorry.py' 'scripts/check_artifact_manifest.py' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' && svm=1
    matches_any "$f" \
      'ProofForge/Evm/**' 'ProofForge/Wasm/**' 'Examples/Evm/**' 'Examples/Xrpl/**' \
      'runtime-tests/evm/**' 'runtime-tests/xrpl/**' 'scripts/check_artifact_manifest.py' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' && evm=1
    matches_any "$f" \
      'ProofForge/Wasm/**' 'Examples/Near/**' 'runtime-tests/near/**' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' && near=1
    matches_any "$f" \
      'Examples/Svm/Phoenix.lean' 'Examples/Svm/PhoenixV1Layout.lean' 'Examples/Svm/PhoenixV1Profile.lean' \
      'Tests/PhoenixBuildSpec.lean' 'Tests/PhoenixSpec.lean' 'Tests/PhoenixV1ProfileSpec.lean' \
      'ProofForge/Svm/AccountStorage/**' 'ProofForge/Svm/FifoCancel/**' 'ProofForge/Svm/BatchRecorder/**' \
      'ProofForge/Svm/Emit.lean' 'runtime-tests/phoenix/**' 'runtime-tests/solana/tests/common/**' \
      'runtime-tests/surfpool/**' && phoenix=1
  done
  if (( shared )); then lean=1; svm=1; evm=1; near=1; phoenix=1; fi
  LANES=()
  (( lean )) && LANES+=(lean)
  (( svm )) && LANES+=(svm)
  (( evm )) && LANES+=(evm)
  (( near )) && LANES+=(near)
  (( phoenix )) && LANES+=(phoenix)
  if ((${#LANES[@]} == 0)); then
    log "docs/website only — running --fast guards"
    FAST=1
    LANES=(guards)
  fi
}

if (( FAST )); then
  LANES=(guards)
elif (( ALL )); then
  LANES=(lean svm evm near phoenix)
elif (( PHOENIX_ONLY )) && ((${#LANES[@]} == 0)); then
  LANES=(phoenix)
elif ((${#LANES[@]} == 0)); then
  detect_lanes
fi

log "lanes: ${LANES[*]-none}  fast=${FAST}"

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
  log "lake build + formalization gates + Tests (no PhoenixTests)"
  lake build
  lake build ProofForgeSvmSdk ProofForgeEvmSdk
  lake build Tests.ProofSpec Tests.SolanalibSpec Tests.SemanticsSpec
  lake build Tests
}

run_svm() {
  log "SVM lane (no Phoenix Mollusk / Surfpool)"
  lake build Examples
  lake exe pf -- build --target svm --out build/sbpf
  python3 scripts/check_artifact_manifest.py --target svm --out build/sbpf
  cargo test --locked --manifest-path runtime-tests/solana/Cargo.toml
  runtime-tests/surfpool/smoke.sh RawEntry
}

run_evm() {
  log "EVM + XRPL lane"
  lake build Examples
  lake exe pf -- build --target evm --out build/evm
  python3 scripts/check_artifact_manifest.py --target evm --out build/evm
  lake exe pf -- build --target xrpl --out build/xrpl
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
  log "NEAR lane (Examples only — no lake build Tests)"
  lake build Examples
  lake exe pf -- build --target near --out build/near
  # Mirror ci.yml NEAR sandbox scripts in order.
  local s
  for s in \
    check counter context bytes ft_event token_arithmetic token_storage memory output \
    storage_balance_output storage_balance_bounds_output \
    json_account_input json_amount_input json_memo_input json_message_input \
    json_ft_transfer_input json_ft_transfer_call_input json_ft_on_transfer_input \
    ft_receiver_value promise_or_value json_ft_resolve_input \
    json_storage_deposit_input json_storage_unregister_input json_storage_withdraw_input \
    json_boolean_mutation storage storage_economics storage_registration \
    vector lookup ledger queue iterable promise
  do
    log "NEAR ${s}"
    "runtime-tests/near/${s}.sh"
  done
}

run_phoenix() {
  log "Phoenix dedicated lane"
  lake build PhoenixExamples PhoenixTests
  lake exe pf -- build --target svm --module Examples.Svm.Phoenix --module Examples.Svm.PhoenixV1Profile --out build/sbpf
  cargo test --locked --manifest-path runtime-tests/phoenix/Cargo.toml
  runtime-tests/surfpool/smoke.sh Phoenix
  runtime-tests/surfpool/smoke.sh PhoenixV1Profile
}

have_lane guards && run_guards
(( FAST )) && run_guards
have_lane lean && run_lean
have_lane svm && run_svm
have_lane evm && run_evm
have_lane near && run_near
have_lane phoenix && run_phoenix

log "ci_local: OK (lanes: ${LANES[*]-none})"
