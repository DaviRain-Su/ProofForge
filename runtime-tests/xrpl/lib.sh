# Shared XRPL local-node helpers. Source after `set -euo pipefail`.
# Missing docker / bedrock → skip (exit 0), not pass. Node start failure → fail closed.

xrpl_root() {
  local here
  here="$(cd "$(dirname "${BASH_SOURCE[1]}")" && pwd)"
  (cd "$here/../.." && pwd)
}

xrpl_find_tool() {
  local name="$1"
  local dir candidate
  if [[ -n "${BEDROCK_BIN:-}" ]]; then
    candidate="${BEDROCK_BIN%/}/$name"
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  fi
  if command -v "$name" >/dev/null 2>&1; then
    command -v "$name"
    return 0
  fi
  for dir in /usr/local/bin "$HOME/.local/bin" "$HOME/go/bin" "$HOME/bin" /opt/homebrew/bin /usr/bin; do
    candidate="$dir/$name"
    if [[ -x "$candidate" ]]; then
      echo "$candidate"
      return 0
    fi
  done
  return 1
}

xrpl_init() {
  local label="${1:-xrpl-local}"
  case "$(uname -s)" in
    Darwin|Linux) ;;
    *)
      echo "$label: skip: unsupported host $(uname -s) (want Darwin or Linux)" >&2
      exit 0
      ;;
  esac
  root="$(xrpl_root)"
  cd "$root"
  docker_bin="$(xrpl_find_tool docker)" || {
    echo "$label: skip: docker not found" >&2
    exit 0
  }
  if [[ -z "${DOCKER_HOST:-}" && -S "/run/user/$(id -u)/docker.sock" ]]; then
    export DOCKER_HOST="unix:///run/user/$(id -u)/docker.sock"
  fi
  if ! "$docker_bin" info >/dev/null 2>&1; then
    echo "$label: skip: docker daemon not running" >&2
    exit 0
  fi
  bedrock="$(xrpl_find_tool bedrock)" || {
    echo "$label: skip: bedrock not found (install XRPL-Commons/bedrock, or set BEDROCK_BIN)" >&2
    exit 0
  }
  python="$(command -v python3 || true)"
  if [[ -z "$python" ]]; then
    echo "$label: skip: python3 not found" >&2
    exit 0
  fi
}

xrpl_require_equal() {
  local actual="$1" expected="$2" message="$3"
  [[ "$actual" == "$expected" ]] || {
    echo "FAIL: $message (expected '$expected', got '$actual')" >&2
    exit 1
  }
}

xrpl_field() {
  local text="$1" label="$2"
  "$python" -I -S -c '
import re, sys
text, label = sys.argv[1], sys.argv[2]
m = re.search(r"(?m)^[ \t]*" + re.escape(label) + r":[ \t]*(.+?)\s*$", text)
if not m:
    raise SystemExit("missing field: " + label)
print(m.group(1).strip())
' "$text" "$label"
}

xrpl_return_code() {
  local text="$1"
  "$python" -I -S -c '
import re, sys
text = sys.argv[1]
m = re.search(r"(?m)^[ \t]*Return Code:[ \t]*(-?\d+)", text)
if not m:
    raise SystemExit("missing Return Code")
print(m.group(1))
' "$text"
}

xrpl_return_decimal() {
  local text="$1"
  "$python" -I -S -c '
import re, sys
text = sys.argv[1]
m = re.search(r"(?m)^[ \t]*Return Value \(decimal\):[ \t]*(-?\d+)", text)
if not m:
    m = re.search(r"(?m)^[ \t]*Return Value:[ \t]*(\S+)", text)
    if not m:
        print(0)
        raise SystemExit
    h = m.group(1).lower()
    if h.startswith("0x"):
        h = h[2:]
    print(int(h, 16) if h else 0)
    raise SystemExit
print(m.group(1))
' "$text"
}

# Standalone genesis account. Bedrock's local funder uses the same seed.
xrpl_genesis_seed() {
  echo "snoPBrXtMeMyMHUVTgbuqAfg1SUTb"
}

xrpl_genesis_address() {
  echo "rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh"
}

# This host does not put view i64 results in meta.ReturnValue. State lives
# in ContractData.ContractJson under the owner account (sfOwner).
xrpl_slot_u64() {
  local owner="$1" contract="$2" key="${3:-value}"
  "$python" -I -S -c '
import json, sys, urllib.request
owner, contract, key = sys.argv[1], sys.argv[2], sys.argv[3]
req = urllib.request.Request(
    "http://localhost:5005",
    data=json.dumps({
        "method": "account_objects",
        "params": [{"account": owner, "ledger_index": "validated"}],
    }).encode(),
    headers={"Content-Type": "application/json"},
)
result = json.load(urllib.request.urlopen(req, timeout=10))["result"]
for obj in result.get("account_objects") or []:
    if obj.get("LedgerEntryType") != "ContractData":
        continue
    if obj.get("ContractAccount") != contract:
        continue
    raw = (obj.get("ContractJson") or {}).get(key)
    if raw is None:
        print(0)
        raise SystemExit
    s = str(raw)
    print(int(s) if s.isdigit() else int(s, 16))
    raise SystemExit
raise SystemExit("missing ContractData for " + contract)
' "$owner" "$contract" "$key"
}
