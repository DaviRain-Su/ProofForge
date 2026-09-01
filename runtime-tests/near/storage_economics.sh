#!/usr/bin/env bash
# Engineering local-node gate for the dynamic storage-usage context leaf.
set -euo pipefail
cd "$(dirname "$0")/../.."

skip() { echo "near-local-storage-economics: skip: $*" >&2; exit 0; }
die() { echo "near-local-storage-economics: FAIL: $*" >&2; exit 1; }

sandbox="${PROOF_FORGE_TOOL_ROOT:-$HOME/.cache/proof-forge-v2/tool-root/linux-x86_64}/near-sandbox"
if [[ ! -x "$sandbox" ]]; then
  command -v near-sandbox >/dev/null 2>&1 || skip "near-sandbox not found"
  sandbox="$(command -v near-sandbox)"
fi
version="$("$sandbox" --version 2>/dev/null || true)"
[[ "$version" == *"release 2.13.0"* ]] || die "near-sandbox 2.13.0 required, got: $version"
python="${PWD}/runtime-tests/near/.venv/bin/python"
[[ -x "$python" ]] || python="$(command -v python3)"
"$python" -c "from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey; import base58" >/dev/null 2>&1 \
  || skip "python cryptography+base58 unavailable"

wasm="${PWD}/build/near/NearStorageEconomics.wasm"
lake exe pf -- build --target near --out build/near NearStorageEconomics
[[ -f "$wasm" ]] || die "missing $wasm"

workdir="$(mktemp -d "${TMPDIR:-/tmp}/near-storage-economics.XXXXXX")"
sandbox_pid=""
cleanup() {
  [[ -z "$sandbox_pid" ]] || ! kill -0 "$sandbox_pid" 2>/dev/null || kill "$sandbox_pid" 2>/dev/null || true
  [[ -z "$sandbox_pid" ]] || wait "$sandbox_pid" 2>/dev/null || true
  rm -rf "$workdir"
}
trap cleanup EXIT
home="$workdir/home"; mkdir -p "$home"; "$sandbox" --home "$home" init >/dev/null
rpc_port="$("$python" -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1]);s.close()')"
net_port="$("$python" -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1]);s.close()')"
"$python" - <<PY
import json
from pathlib import Path
p=Path("$home")/"config.json"; c=json.loads(p.read_text())
c.setdefault("rpc",{})["addr"]="127.0.0.1:${rpc_port}"
c.setdefault("network",{})["addr"]="127.0.0.1:${net_port}"; c["network"]["boot_nodes"]=""
p.write_text(json.dumps(c,indent=2)+"\n")
PY
"$sandbox" --home "$home" run >"$workdir/node.log" 2>&1 & sandbox_pid=$!
rpc="http://127.0.0.1:${rpc_port}"
ready=0
for _ in $(seq 1 90); do
  if curl -sf -X POST "$rpc" -H 'content-type: application/json' -d '{"jsonrpc":"2.0","id":"1","method":"status","params":[]}' >/dev/null; then ready=1; break; fi
  kill -0 "$sandbox_pid" 2>/dev/null || { tail -80 "$workdir/node.log" >&2; die "sandbox exited"; }
  sleep 0.5
done
[[ "$ready" -eq 1 ]] || die "sandbox RPC not ready"
export PF_NEAR_RPC="$rpc" PF_NEAR_HOME="$home" PF_NEAR_WASM="$wasm"
export PYTHONPATH="${PWD}/runtime-tests/near${PYTHONPATH:+:$PYTHONPATH}"
"$python" runtime-tests/near/storage_economics.py
echo "near-local-storage-economics: ok"
