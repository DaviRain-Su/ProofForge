#!/usr/bin/env node
// Submit a ContractCall with STArray-wrapped Parameters over HTTP JSON-RPC.
// bedrock call currently omits the outer { Parameter: ... } wrapper.
"use strict";

const fs = require("fs");
const path = require("path");

function loadXrpl() {
  const roots = [
    path.join(process.env.HOME || "", ".cache/bedrock/modules/contract/node_modules"),
    path.join(process.env.HOME || "", ".cache/bedrock/modules/node_modules"),
  ];
  for (const root of roots) {
    try {
      return require(path.join(root, "@xrpl-commons/xrpl"));
    } catch (_) {}
    try {
      return require(path.join(root, "xrpl"));
    } catch (_) {}
  }
  throw new Error("could not load @xrpl-commons/xrpl");
}

function rpcUrl(wsUrl) {
  if (wsUrl.startsWith("ws://")) {
    return "http://" + wsUrl.slice("ws://".length);
  }
  if (wsUrl.startsWith("wss://")) {
    return "https://" + wsUrl.slice("wss://".length);
  }
  return wsUrl;
}

async function rpc(url, method, params) {
  const body = JSON.stringify({ method, params: [params || {}] });
  const res = await fetch(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body,
  });
  if (!res.ok) {
    throw new Error(`rpc ${method} HTTP ${res.status}`);
  }
  const json = await res.json();
  if (json.result && json.result.error) {
    const err = new Error(json.result.error_message || json.result.error);
    err.code = json.result.error;
    throw err;
  }
  if (json.error) {
    throw new Error(json.error_message || json.error);
  }
  return json.result;
}

function formatValue(type, value) {
  if (value === undefined || value === null) {
    throw new Error(`missing parameter value for type ${type}`);
  }
  return { type, value: String(value) };
}

function buildParameters(fn, values) {
  if (!fn.parameters || fn.parameters.length === 0) {
    return undefined;
  }
  return fn.parameters.map((param, i) => {
    const raw = values[param.name] !== undefined ? values[param.name] : values[i];
    if (raw === undefined) {
      throw new Error(`missing argument ${param.name}`);
    }
    return {
      Parameter: {
        ParameterFlag: param.flag || 0,
        ParameterValue: formatValue(param.type, raw),
      },
    };
  });
}

async function waitValidated(url, hash) {
  const deadline = Date.now() + 60000;
  while (Date.now() < deadline) {
    try {
      const result = await rpc(url, "tx", { transaction: hash });
      if (result.validated || result.meta) {
        return result;
      }
    } catch (_) {}
    await new Promise((r) => setTimeout(r, 400));
  }
  throw new Error(`transaction ${hash} not validated in 60s`);
}

async function main() {
  const cfg = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
  const xrpl = loadXrpl();
  const { Wallet, encode } = xrpl;
  const url = cfg.rpc_url || rpcUrl(cfg.network_url).replace(/:6006$/, ":5005");
  const wallet = Wallet.fromSeed(cfg.wallet_seed, { algorithm: "secp256k1" });
  const abi = JSON.parse(fs.readFileSync(cfg.abi_path, "utf8"));
  const fn = abi.functions.find((f) => f.name === cfg.function_name);
  if (!fn) {
    throw new Error(`function ${cfg.function_name} not in ABI`);
  }
  const Parameters = buildParameters(fn, cfg.parameters || {});
  let accountInfo;
  for (let i = 0; i < 20; i++) {
    try {
      accountInfo = await rpc(url, "account_info", {
        account: wallet.address,
        ledger_index: "current",
      });
      break;
    } catch (err) {
      if (i === 19) {
        err.message = `account_info ${wallet.address}: ${err.message}`;
        throw err;
      }
      await new Promise((r) => setTimeout(r, 500));
    }
  }
  const tx = {
    TransactionType: "ContractCall",
    Account: wallet.address,
    ContractAccount: cfg.contract_account,
    FunctionName: Buffer.from(cfg.function_name).toString("hex").toUpperCase(),
    ComputationAllowance: parseInt(cfg.computation_allowance || "1000000", 10),
    Fee: cfg.fee || "1000000",
    Sequence: accountInfo.account_data.Sequence,
    SigningPubKey: wallet.publicKey,
  };
  if (Parameters) {
    tx.Parameters = Parameters;
  }
  const signed = wallet.sign(tx);
  const submitted = await rpc(url, "submit", { tx_blob: signed.tx_blob });
  if (submitted.engine_result !== "tesSUCCESS") {
    throw new Error(
      `submit ${cfg.function_name}: ${submitted.engine_result} ${submitted.engine_result_message || ""}`
    );
  }
  const result = await waitValidated(url, signed.hash);
  const meta = result.meta || {};
  process.stdout.write(
    JSON.stringify({
      success: meta.TransactionResult === "tesSUCCESS",
      txHash: signed.hash,
      returnCode: meta.WasmReturnCode ?? meta.ReturnCode ?? null,
      returnValue: meta.ReturnValue ?? null,
      transactionResult: meta.TransactionResult ?? null,
    }) + "\n"
  );
}

main().catch((err) => {
  process.stderr.write(String(err && err.stack ? err.stack : err) + "\n");
  process.exit(1);
});
