#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
skip() { echo "near-local-promise-or-value: skip: $*" >&2; exit 0; }
die() { echo "near-local-promise-or-value: FAIL: $*" >&2; exit 1; }
sandbox="${PROOF_FORGE_TOOL_ROOT:-$HOME/.cache/proof-forge-v2/tool-root/linux-x86_64}/near-sandbox"
if [[ ! -x "$sandbox" ]]; then command -v near-sandbox >/dev/null 2>&1 && sandbox="$(command -v near-sandbox)" || skip "near-sandbox not found"; fi
[[ "$("$sandbox" --version 2>/dev/null || true)" == *"release 2.13.0"* ]] || die "near-sandbox 2.13.0 required"
python="${PWD}/runtime-tests/near/.venv/bin/python"; [[ -x "$python" ]] || python="$(command -v python3)"
"$python" -c "from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey; import base58" >/dev/null 2>&1 || skip "python dependencies unavailable"
lake exe pf -- build --target near --out build/near NearPromiseOrValue NearPromise
workdir="$(mktemp -d "${TMPDIR:-/tmp}/near-promise-or-value.XXXXXX")"; pid=""
cleanup() { if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; fi; rm -rf "$workdir"; }; trap cleanup EXIT
home="$workdir/home"; mkdir -p "$home"; "$sandbox" --home "$home" init >/dev/null
read -r rpc_port net_port < <("$python" - <<'PY'
import socket
def port():
 s=socket.socket(); s.bind(("127.0.0.1",0)); p=s.getsockname()[1]; s.close(); return p
print(port(), port())
PY
)
"$python" - <<PY
import json
from pathlib import Path
p=Path("$home")/"config.json"; c=json.loads(p.read_text()); c.setdefault("rpc",{})["addr"]="127.0.0.1:${rpc_port}"; c.setdefault("network",{})["addr"]="127.0.0.1:${net_port}"; c["network"]["boot_nodes"]=""; p.write_text(json.dumps(c,indent=2)+"\n")
PY
"$sandbox" --home "$home" run >"$workdir/node.log" 2>&1 & pid=$!
rpc="http://127.0.0.1:${rpc_port}"
for _ in $(seq 1 90); do curl -sf -X POST "$rpc" -H 'content-type: application/json' -d '{"jsonrpc":"2.0","id":"1","method":"status","params":[]}' >/dev/null 2>&1 && break; sleep .5; done
curl -sf -X POST "$rpc" -H 'content-type: application/json' -d '{"jsonrpc":"2.0","id":"1","method":"status","params":[]}' >/dev/null || die "RPC not ready"
export PF_NEAR_RPC="$rpc" PF_NEAR_HOME="$home" PF_NEAR_POV_WASM="${PWD}/build/near/NearPromiseOrValue.wasm" PF_NEAR_PROMISE_WASM="${PWD}/build/near/NearPromise.wasm" PYTHONPATH="${PWD}/runtime-tests/near${PYTHONPATH:+:$PYTHONPATH}"
"$python" runtime-tests/near/promise_or_value.py
echo "near-local-promise-or-value: ok"
