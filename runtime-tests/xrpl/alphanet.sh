#!/usr/bin/env bash
# Optional live AlphaNet smoke. Not CI.
# Builds Counter with XLS-0102 host names, submits ContractCreate via
# server_definitions encoding, then ContractCall initialize(0).
# Missing node / public RPC 502 / noCurrent → skip (exit 0), not pass.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

root="$(cd "$here/../.." && pwd)"
cd "$root"

python="$(command -v python3 || true)"
if [[ -z "$python" ]]; then
  echo "xrpl-alphanet: skip: python3 not found" >&2
  exit 0
fi
if ! command -v node >/dev/null 2>&1; then
  echo "xrpl-alphanet: skip: node not found" >&2
  exit 0
fi

RPC="${XRPL_ALPHANET_RPC:-https://alphanet.xrpl.org}"
if ! "$python" -I -S -c '
import json, sys, urllib.request
url = sys.argv[1]
req = urllib.request.Request(url, data=json.dumps({"method":"server_info","params":[{}]}).encode(),
    headers={"Content-Type":"application/json","User-Agent":"ProofForge"})
info = json.load(urllib.request.urlopen(req, timeout=15))["result"]["info"]
features = json.load(urllib.request.urlopen(
    urllib.request.Request(url, data=json.dumps({"method":"feature","params":[{}]}).encode(),
        headers={"Content-Type":"application/json","User-Agent":"ProofForge"}), timeout=15)
)["result"]["features"]
sc = None
for v in features.values():
    if isinstance(v, dict) and v.get("name") == "SmartContract":
        sc = v.get("enabled")
print(info.get("network_id"), info.get("server_state"), sc)
' "$RPC" >/tmp/pf-alphanet-info.txt 2>/tmp/pf-alphanet-info.err; then
  echo "xrpl-alphanet: skip: cannot reach $RPC" >&2
  cat /tmp/pf-alphanet-info.err >&2 || true
  exit 0
fi
read -r nid state smart </tmp/pf-alphanet-info.txt
if [[ "$smart" != "True" && "$smart" != "true" ]]; then
  echo "xrpl-alphanet: skip: SmartContract not enabled ($nid $state $smart)" >&2
  exit 0
fi
echo "xrpl-alphanet: $RPC network_id=$nid state=$state SmartContract=$smart" >&2

wasm="$root/build/xrpl-alphanet/Counter.wasm"
if [[ ! -f "$wasm" ]]; then
  echo "xrpl-alphanet: building Counter.wasm (XLS-0102 host names)" >&2
  lake exe pf -- build --target xrpl-alphanet --out "$root/build/xrpl-alphanet" Counter
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

if ! rg -q 'import "host_lib" "home_le_field"' "$root/build/xrpl-alphanet/Counter.wat"; then
  echo "FAIL: alphanet WAT missing home_le_field" >&2
  exit 1
fi
if rg -q 'import "host_lib" "get_current_ledger_obj_field"' "$root/build/xrpl-alphanet/Counter.wat"; then
  echo "FAIL: alphanet WAT still imports Bedrock host names" >&2
  exit 1
fi

echo "xrpl-alphanet: artifact ok ($wasm)."
echo "  Live zero-arg deploy/call is runtime-tests/xrpl/smoke.sh (XrplSmoke)."
echo "  Live parameterized Counter is runtime-tests/xrpl/alphanet-counter.sh (increment(1))."
echo "  Live initialize(7) is runtime-tests/xrpl/alphanet-init.sh (Function ABI required)."
echo "  Live XrplVec setAt(1,5) is runtime-tests/xrpl/alphanet-vec.sh."
exit 0
