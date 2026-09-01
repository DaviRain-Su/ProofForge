#!/usr/bin/env bash
# Engineering local-node gate for detached and returned static cross-contract calls.
set -euo pipefail
cd "$(dirname "$0")/../.."

skip() {
  echo "near-local-promise: skip: $*" >&2
  exit 0
}

die() {
  echo "near-local-promise: FAIL: $*" >&2
  exit 1
}

sandbox="${PROOF_FORGE_TOOL_ROOT:-$HOME/.cache/proof-forge-v2/tool-root/linux-x86_64}/near-sandbox"
if [[ ! -x "$sandbox" ]]; then
  if command -v near-sandbox >/dev/null 2>&1; then
    sandbox="$(command -v near-sandbox)"
  else
    skip "near-sandbox not found"
  fi
fi
version="$("$sandbox" --version 2>/dev/null || true)"
if [[ -z "$version" ]]; then
  skip "near-sandbox present but not runnable on this host"
fi
[[ "$version" == *"release 2.13.0"* ]] || die "near-sandbox 2.13.0 required, got: $version"

python="${PWD}/runtime-tests/near/.venv/bin/python"
if [[ ! -x "$python" ]]; then
  python="$(command -v python3)"
fi
if ! "$python" -c "from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey; import base58" >/dev/null 2>&1; then
  skip "python cryptography+base58 unavailable (see runtime-tests/near/requirements.txt)"
fi

wasm="${PWD}/build/near/NearPromise.wasm"
echo "near-local-promise: building NearPromise.wasm" >&2
lake exe pf -- build --target near --out build/near NearPromise
[[ -f "$wasm" ]] || die "missing $wasm"
"$python" -I -S -c 'import sys; raise SystemExit(0 if open(sys.argv[1], "rb").read(4) == b"\x00asm" else 1)' "$wasm" \
  || die "$wasm is not wasm"

workdir="$(mktemp -d "${TMPDIR:-/tmp}/near-promise.XXXXXX")"
sandbox_pid=""
cleanup() {
  if [[ -n "${sandbox_pid:-}" ]] && kill -0 "$sandbox_pid" 2>/dev/null; then
    kill "$sandbox_pid" 2>/dev/null || true
    wait "$sandbox_pid" 2>/dev/null || true
  fi
  rm -rf "$workdir"
}
trap cleanup EXIT

wat2wasm="${PROOF_FORGE_WAT2WASM:-$HOME/.local/bin/wat2wasm}"
if [[ ! -x "$wat2wasm" ]]; then
  wat2wasm="$(command -v wat2wasm || true)"
fi
[[ -x "$wat2wasm" ]] || skip "wat2wasm 1.0.41 not found"
[[ "$($wat2wasm --version 2>/dev/null)" == "1.0.41" ]] ||
  die "wat2wasm 1.0.41 required for observer fixture"
observer_wasm="$workdir/ft-on-transfer-observer.wasm"
"$wat2wasm" runtime-tests/near/fixture/ft-on-transfer-observer.wat -o "$observer_wasm"
[[ -f "$observer_wasm" ]] || die "observer fixture assembly produced no wasm"
quoted_result_wasm="$workdir/quoted-u128-results.wasm"
"$wat2wasm" runtime-tests/near/fixture/quoted-u128-results.wat -o "$quoted_result_wasm"
[[ -f "$quoted_result_wasm" ]] || die "quoted-u128 result fixture assembly produced no wasm"

home="$workdir/home"
mkdir -p "$home"
echo "near-local-promise: near-sandbox init --home $home" >&2
"$sandbox" --home "$home" init >/dev/null

rpc_port="$("$python" - <<'PY'
import socket
s = socket.socket()
s.bind(("127.0.0.1", 0))
print(s.getsockname()[1])
s.close()
PY
)"
net_port="$("$python" - <<'PY'
import socket
s = socket.socket()
s.bind(("127.0.0.1", 0))
print(s.getsockname()[1])
s.close()
PY
)"
"$python" - <<PY
import json
from pathlib import Path
cfg_path = Path("$home") / "config.json"
cfg = json.loads(cfg_path.read_text())
cfg.setdefault("rpc", {})["addr"] = "127.0.0.1:${rpc_port}"
cfg.setdefault("network", {})["addr"] = "127.0.0.1:${net_port}"
cfg.setdefault("network", {})["boot_nodes"] = ""
cfg_path.write_text(json.dumps(cfg, indent=2) + "\n")
PY

echo "near-local-promise: starting node rpc=127.0.0.1:${rpc_port}" >&2
"$sandbox" --home "$home" run >"$workdir/node.log" 2>&1 &
sandbox_pid=$!

rpc="http://127.0.0.1:${rpc_port}"
ready=0
for _ in $(seq 1 90); do
  if curl -sf -X POST "$rpc" \
      -H 'content-type: application/json' \
      -d '{"jsonrpc":"2.0","id":"1","method":"status","params":[]}' \
      >/dev/null 2>&1; then
    ready=1
    break
  fi
  if ! kill -0 "$sandbox_pid" 2>/dev/null; then
    tail -80 "$workdir/node.log" >&2 || true
    die "near-sandbox exited early"
  fi
  sleep 0.5
done
[[ "$ready" -eq 1 ]] || {
  tail -80 "$workdir/node.log" >&2 || true
  die "near-sandbox RPC not ready"
}

export PF_NEAR_RPC="$rpc"
export PF_NEAR_HOME="$home"
export PF_NEAR_WASM="$wasm"
export PF_NEAR_OBSERVER_WASM="$observer_wasm"
export PF_NEAR_QUOTED_RESULT_WASM="$quoted_result_wasm"
export PYTHONPATH="${PWD}/runtime-tests/near${PYTHONPATH:+:$PYTHONPATH}"
echo "near-local-promise: RPC ready; running static calls + self-callback scenes" >&2
"$python" runtime-tests/near/promise.py
echo "near-local-promise: ok"
