#!/usr/bin/env bash
# Local productization smoke (prod-002..004). Run from repo root with elan + sbpf + solc on PATH.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PATH="${HOME}/.elan/bin:${HOME}/.cargo/bin:${HOME}/.local/bin:/usr/local/bin:${PATH}"

python3 scripts/check_ownership.py
python3 scripts/check_sdk_import_closure.py
lake build ProofForgeSvmSdk ProofForgeEvmSdk pf

echo "== registry Counter (digest-pinned) =="
rm -rf /tmp/pf-smoke-svm /tmp/pf-smoke-evm
lake exe pf -- build --target svm --module Examples.Counter --out /tmp/pf-smoke-svm
lake exe pf -- build --target evm --module Examples.Counter --out /tmp/pf-smoke-evm
test -f /tmp/pf-smoke-svm/Counter.so
test -f /tmp/pf-smoke-evm/Counter.bin

echo "== pf init templates =="
rm -rf /tmp/pf-smoke-init-svm /tmp/pf-smoke-init-evm
# init into sibling dirs under /tmp won't path-require monorepo; use repo-local scratch
rm -rf .smoke-svm .smoke-evm
lake exe pf -- init .smoke-svm --target svm
lake exe pf -- init .smoke-evm --target evm
( cd .smoke-svm && lake build && lake exe pf -- build --target svm --module MyProgram.Counter --out build/out && test -f build/out/Counter.so )
( cd .smoke-evm && lake build && lake exe pf -- build --target evm --module MyContract.Counter --out build/out && test -f build/out/Counter.bin )
rm -rf .smoke-svm .smoke-evm

lake exe pf -- --version
echo "smoke_productization: ok"
