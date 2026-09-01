#!/usr/bin/env bash
# Engineering local-node gate for XrplOwn three-limb compare.
# Missing docker/bedrock → skip (exit 0). Deploys ProofForge XrplOwn.wasm only.
# Genesis init+bump changes value; a second funded account bump returns 3 and
# leaves the slot unchanged. No eq_account host.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=runtime-tests/xrpl/lib.sh
source "$here/lib.sh"

xrpl_init xrpl-local-own

wasm="$root/build/xrpl/XrplOwn.wasm"
fixture="$here/fixture"
staged="$fixture/contract/target/wasm32-unknown-unknown/release/Counter.wasm"

if [[ ! -f "$wasm" ]]; then
  echo "xrpl-local-own: building XrplOwn.wasm" >&2
  lake exe pf -- build --target xrpl --out "$root/build/xrpl"
fi
[[ -f "$wasm" ]] || { echo "FAIL: missing $wasm" >&2; exit 1; }

mkdir -p "$(dirname "$staged")"
cp -f "$wasm" "$staged"
mkdir -p "$fixture/.bedrock/node-config"
rm -rf "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/xrpld.cfg" "$fixture/.bedrock/node-config/xrpld.cfg"
cp -f "$fixture/node-config/genesis.json" "$fixture/.bedrock/node-config/genesis.json"

cleanup() {
  if [[ -n "${bedrock:-}" ]]; then
    (cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
  fi
}
trap cleanup EXIT

echo "xrpl-local-own: starting local node" >&2
(cd "$fixture" && "$bedrock" node stop >/dev/null 2>&1) || true
(cd "$fixture" && "$bedrock" node start)

wallet="$(xrpl_genesis_seed)"
owner="$(xrpl_genesis_address)"
# Deterministic secp256k1 account, funded by genesis Payment. Not the owner.
other_seed="sp8y8kecNjy88BZRr9U991iiRzFNf"
other_addr="rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG"

deploy_out="$(cd "$fixture" && "$bedrock" deploy \
  --network local \
  --skip-build \
  --skip-abi \
  --abi abi.json \
  --wallet "$wallet")"
echo "$deploy_out" >&2

contract="$(xrpl_field "$deploy_out" "Contract Account")"
[[ -n "$contract" ]] || {
  echo "FAIL: deploy did not return Contract Account: $deploy_out" >&2
  exit 1
}

xrpl_call() {
  local seed="$1"
  local fn="$2"
  local params="{}"
  if [[ -n "${3:-}" ]]; then
    params="$3"
  fi
  local cfg
  cfg="$(mktemp)"
  XRPL_CFG="$cfg" \
  XRPL_CONTRACT="$contract" XRPL_FN="$fn" XRPL_WALLET="$seed" \
    XRPL_ABI="$fixture/abi.json" XRPL_PARAMS="$params" \
    "$python" -I -S -c '
import json, os
json.dump({
    "contract_account": os.environ["XRPL_CONTRACT"],
    "function_name": os.environ["XRPL_FN"],
    "network_url": "ws://localhost:6006",
    "wallet_seed": os.environ["XRPL_WALLET"],
    "abi_path": os.environ["XRPL_ABI"],
    "parameters": json.loads(os.environ.get("XRPL_PARAMS") or "{}"),
}, open(os.environ["XRPL_CFG"], "w", encoding="utf-8"))
'
  local out
  out="$(node "$here/call.js" "$cfg")"
  rm -f "$cfg"
  printf '%s\n' "$out"
}

xrpl_call_code() {
  "$python" -I -S -c 'import json,sys; print(json.load(sys.stdin).get("returnCode"))' <<<"$1"
}

xrpl_pay() {
  local src_seed="$1"
  local dest="$2"
  local drops="$3"
  XRPL_SRC="$src_seed" XRPL_DEST="$dest" XRPL_DROPS="$drops" \
    node -e '
const path = require("path");
const fs = require("fs");
const roots = [
  path.join(process.env.HOME || "", ".cache/bedrock/modules/contract/node_modules/@xrpl-commons/xrpl"),
  path.join(process.env.HOME || "", ".cache/bedrock/modules/node_modules/@xrpl-commons/xrpl"),
];
let xrpl;
for (const root of roots) {
  try { xrpl = require(root); break; } catch (_) {}
}
if (!xrpl) throw new Error("could not load @xrpl-commons/xrpl");
const { Wallet } = xrpl;
const url = "http://localhost:5005";
async function rpc(method, params) {
  const res = await fetch(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ method, params: [params || {}] }),
  });
  if (!res.ok) throw new Error("rpc " + method + " HTTP " + res.status);
  const json = await res.json();
  if (json.result && json.result.error) {
    throw new Error(json.result.error_message || json.result.error);
  }
  return json.result;
}
(async () => {
  const wallet = Wallet.fromSeed(process.env.XRPL_SRC, { algorithm: "secp256k1" });
  let accountInfo;
  for (let i = 0; i < 20; i++) {
    try {
      accountInfo = await rpc("account_info", { account: wallet.address, ledger_index: "current" });
      break;
    } catch (err) {
      if (i === 19) throw err;
      await new Promise((r) => setTimeout(r, 500));
    }
  }
  const tx = {
    TransactionType: "Payment",
    Account: wallet.address,
    Destination: process.env.XRPL_DEST,
    Amount: process.env.XRPL_DROPS,
    Fee: "1000000",
    Sequence: accountInfo.account_data.Sequence,
    SigningPubKey: wallet.publicKey,
  };
  const signed = wallet.sign(tx);
  const submitted = await rpc("submit", { tx_blob: signed.tx_blob });
  if (submitted.engine_result !== "tesSUCCESS") {
    throw new Error("pay: " + submitted.engine_result + " " + (submitted.engine_result_message || ""));
  }
  const deadline = Date.now() + 60000;
  while (Date.now() < deadline) {
    try {
      const result = await rpc("tx", { transaction: signed.hash });
      if (result.validated || result.meta) {
        if ((result.meta || {}).TransactionResult !== "tesSUCCESS") {
          throw new Error("pay meta: " + ((result.meta || {}).TransactionResult));
        }
        process.stdout.write("paid " + process.env.XRPL_DEST + "\n");
        return;
      }
    } catch (err) {
      if (String(err).includes("pay meta:")) throw err;
    }
    await new Promise((r) => setTimeout(r, 400));
  }
  throw new Error("pay not validated");
})().catch((err) => {
  process.stderr.write(String(err && err.stack ? err.stack : err) + "\\n");
  process.exit(1);
});
'
}

init_out="$(xrpl_call "$wallet" initialize '{"initial_value":"0"}')"
xrpl_require_equal "$(xrpl_call_code "$init_out")" "0" "initialize status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "value")" "0" "initialize value"

bump_out="$(xrpl_call "$wallet" bump '{}')"
xrpl_require_equal "$(xrpl_call_code "$bump_out")" "0" "owner bump status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "value")" "1" "owner bump value"

echo "xrpl-local-own: funding second account $other_addr" >&2
xrpl_pay "$wallet" "$other_addr" "10000000000"

other_out="$(xrpl_call "$other_seed" bump '{}')"
xrpl_require_equal "$(xrpl_call_code "$other_out")" "3" "non-owner bump status"
xrpl_require_equal "$(xrpl_slot_u64 "$owner" "$contract" "value")" "1" \
  "non-owner bump must leave value"

echo "xrpl-local-own: ok (owner bump=1; other bump status=3; engineering only)"
