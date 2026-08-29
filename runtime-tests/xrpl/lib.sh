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
  for dir in /usr/local/bin "$HOME/.local/bin" /opt/homebrew/bin /usr/bin; do
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
  if ! "$docker_bin" info >/dev/null 2>&1; then
    echo "$label: skip: docker daemon not running" >&2
    exit 0
  fi
  bedrock="$(xrpl_find_tool bedrock)" || {
    echo "$label: skip: bedrock not found (install XRPL-Commons/bedrock, or set BEDROCK_BIN)" >&2
    exit 0
  }
  jq_bin="$(xrpl_find_tool jq)" || {
    echo "$label: skip: jq not found" >&2
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

xrpl_extract_json() {
  "$python" -I -S -c '
import json, sys
text = sys.stdin.read()
decoder = json.JSONDecoder()
found = None
i = 0
while i < len(text):
    if text[i] == "{":
        try:
            obj, end = decoder.raw_decode(text, i)
            found = obj
            i = end
            continue
        except json.JSONDecodeError:
            pass
    i += 1
if found is None:
    raise SystemExit("no JSON object in command output")
json.dump(found, sys.stdout)
' <<<"$1"
}

xrpl_json_field() {
  local json="$1" path="$2"
  xrpl_extract_json "$json" | "$jq_bin" -er "$path"
}

xrpl_hex_u64() {
  local hex="$1"
  "$python" -I -S -c '
import sys
h = sys.argv[1].strip().lower()
if h.startswith("0x"):
    h = h[2:]
if h == "" or h == "null":
    print(0)
    raise SystemExit
if len(h) % 2:
    h = "0" + h
print(int(h, 16))
' "$hex"
}
