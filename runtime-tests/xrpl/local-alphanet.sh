#!/usr/bin/env bash
# Start a local SmartContract standalone node (transia/alphanet).
# This is dangell/smart-contracts 2.6.1-rc1, NOT the public 3.3.0-rc1
# and NOT the Bedrock vault image. Missing docker → skip.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

label=xrpl-local-alphanet
case "$(uname -s)" in
  Darwin|Linux) ;;
  *)
    echo "$label: skip: unsupported host $(uname -s)" >&2
    exit 0
    ;;
esac
if [[ -z "${DOCKER_HOST:-}" && -S "/run/user/$(id -u)/docker.sock" ]]; then
  export DOCKER_HOST="unix:///run/user/$(id -u)/docker.sock"
fi
docker_bin="$(xrpl_find_tool docker)" || {
  echo "$label: skip: docker not found" >&2
  exit 0
}
if ! "$docker_bin" info >/dev/null 2>&1; then
  echo "$label: skip: docker daemon not running" >&2
  exit 0
fi

name="${XRPL_LOCAL_NAME:-pf-alphanet-local}"
rpc_port="${XRPL_LOCAL_RPC_PORT:-15005}"
image="${XRPL_LOCAL_IMAGE:-transia/alphanet:latest}"
cmd="${1:-up}"

case "$cmd" in
  up|start)
    if "$docker_bin" inspect "$name" >/dev/null 2>&1; then
      state="$("$docker_bin" inspect -f '{{.State.Running}}' "$name")"
      if [[ "$state" == "true" ]]; then
        echo "$label: already running $name" >&2
        exit 0
      fi
      "$docker_bin" rm -f "$name" >/dev/null
    fi
    "$docker_bin" pull "$image" >/dev/null
    "$docker_bin" run -d --name "$name" \
      -p "127.0.0.1:${rpc_port}:5005" \
      "$image" >/dev/null
    for i in $(seq 1 30); do
      if curl -sS -m 1 -X POST "http://127.0.0.1:${rpc_port}" \
          -H 'Content-Type: application/json' \
          -d '{"method":"server_info","params":[{}]}' \
          | python3 -I -S -c 'import json,sys; d=json.load(sys.stdin); assert d["result"]["info"]["server_state"]' \
          >/dev/null 2>&1; then
        echo "$label: up rpc=http://127.0.0.1:${rpc_port} image=$image" >&2
        exit 0
      fi
      sleep 1
    done
    echo "$label: FAIL: node did not answer server_info" >&2
    "$docker_bin" logs "$name" >&2 || true
    exit 1
    ;;
  down|stop)
    "$docker_bin" rm -f "$name" >/dev/null 2>&1 || true
    echo "$label: stopped $name" >&2
    ;;
  *)
    echo "usage: $0 up|down" >&2
    exit 1
    ;;
esac
