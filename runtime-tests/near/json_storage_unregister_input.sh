#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
skip() { echo "near-local-json-storage-unregister-input: skip: $*" >&2; exit 0; }
die() { echo "near-local-json-storage-unregister-input: FAIL: $*" >&2; exit 1; }
sandbox="${PROOF_FORGE_TOOL_ROOT:-$HOME/.cache/proof-forge-v2/tool-root/linux-x86_64}/near-sandbox"
if [[ ! -x "$sandbox" ]]; then
  if command -v near-sandbox >/dev/null 2>&1; then sandbox="$(command -v near-sandbox)"; else skip "near-sandbox not found"; fi
fi
version="$("$sandbox" --version 2>/dev/null || true)"
[[ "$version" == *"release 2.13.0"* ]] || die "near-sandbox 2.13.0 required, got: $version"
python="${PWD}/runtime-tests/near/.venv/bin/python"; [[ -x "$python" ]] || python="$(command -v python3)"
if ! "$python" -c "from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey; import base58" >/dev/null 2>&1; then
  skip "python cryptography+base58 unavailable"
fi
wasm="${PWD}/build/near/NearJsonStorageUnregisterInput.wasm"
lake exe pf -- build --target near --out build/near NearJsonStorageUnregisterInput
[[ -f "$wasm" ]] || die "missing $wasm"
workdir="$(mktemp -d "${TMPDIR:-/tmp}/near-json-storage-unregister-input.XXXXXX")"; sandbox_pid=""
cleanup() { if [[ -n "$sandbox_pid" ]] && kill -0 "$sandbox_pid" 2>/dev/null; then kill "$sandbox_pid" 2>/dev/null || true; wait "$sandbox_pid" 2>/dev/null || true; fi; rm -rf "$workdir"; }
trap cleanup EXIT
home="$workdir/home"; mkdir -p "$home"; "$sandbox" --home "$home" init >/dev/null
rpc_port="$("$python" - <<'PY'
import socket
s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()
PY
)"
net_port="$("$python" - <<'PY'
import socket
s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()
PY
)"
"$python" - <<PY
import json
from pathlib import Path
p=Path("$home")/"config.json"; c=json.loads(p.read_text()); c.setdefault("rpc",{})["addr"]="127.0.0.1:${rpc_port}"; c.setdefault("network",{})["addr"]="127.0.0.1:${net_port}"; c["network"]["boot_nodes"]=""; p.write_text(json.dumps(c,indent=2)+"\n")
PY
"$sandbox" --home "$home" run >"$workdir/node.log" 2>&1 & sandbox_pid=$!
rpc="http://127.0.0.1:${rpc_port}"; ready=0
for _ in $(seq 1 90); do
  if curl -sf -X POST "$rpc" -H 'content-type: application/json' -d '{"jsonrpc":"2.0","id":"1","method":"status","params":[]}' >/dev/null 2>&1; then ready=1; break; fi
  if ! kill -0 "$sandbox_pid" 2>/dev/null; then tail -80 "$workdir/node.log" >&2 || true; die "near-sandbox exited early"; fi
  sleep 0.5
done
[[ "$ready" -eq 1 ]] || die "RPC not ready"
export PF_NEAR_RPC="$rpc" PF_NEAR_HOME="$home" PF_NEAR_WASM="$wasm" PYTHONPATH="${PWD}/runtime-tests/near${PYTHONPATH:+:$PYTHONPATH}"
"$python" runtime-tests/near/json_storage_unregister_input.py
echo "near-local-json-storage-unregister-input: ok"
