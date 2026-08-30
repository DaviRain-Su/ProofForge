#!/usr/bin/env node
// ProofForge AlphaNet JSON-RPC helper. Uses node-signed blobs when possible,
// otherwise signs with server_definitions from the same RPC.
"use strict";

const fs = require("fs");
const https = require("https");
const http = require("http");
const path = require("path");

function loadXrpl() {
  const roots = [
    path.join(process.env.HOME || "", ".cache/bedrock/modules/contract/node_modules"),
    path.join(__dirname, "node_modules"),
  ];
  for (const root of roots) {
    try {
      return {
        xrpl: require(path.join(root, "@xrpl-commons/xrpl")),
        codec: require(path.join(root, "@xrpl-commons/ripple-binary-codec")),
        keypairs: require(path.join(root, "@xrpl-commons/ripple-keypairs")),
      };
    } catch (_) {}
  }
  throw new Error("could not load @xrpl-commons/xrpl (install bedrock cache or local node_modules)");
}

function rpc(url, method, params, timeoutMs) {
  const payload = JSON.stringify({ method, params: [params || {}] });
  const parsed = new URL(url);
  const lib = parsed.protocol === "https:" ? https : http;
  return new Promise((resolve, reject) => {
    const req = lib.request(
      {
        hostname: parsed.hostname,
        port: parsed.port,
        path: parsed.pathname && parsed.pathname !== "" ? parsed.pathname : "/",
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "Content-Length": Buffer.byteLength(payload),
          "User-Agent": "ProofForge",
        },
      },
      (res) => {
        let data = "";
        res.on("data", (c) => {
          data += c;
        });
        res.on("end", () => {
          if (res.statusCode >= 500) {
            reject(new Error("http " + res.statusCode));
            return;
          }
          try {
            const json = JSON.parse(data);
            if (json.result && json.result.error) {
              const err = new Error(json.result.error_message || json.result.error);
              err.full = json.result;
              reject(err);
              return;
            }
            resolve(json.result);
          } catch (e) {
            reject(new Error("rpc parse: " + data.slice(0, 200)));
          }
        });
      }
    );
    req.on("error", reject);
    req.setTimeout(timeoutMs || 25000, () => {
      req.destroy();
      reject(new Error("timeout"));
    });
    req.write(payload);
    req.end();
  });
}

async function rpcRetry(url, method, params, tries) {
  let last;
  for (let i = 0; i < (tries || 6); i++) {
    try {
      return await rpc(url, method, params);
    } catch (e) {
      last = e;
      const msg = String(e.message || e);
      if (
        msg.startsWith("http ") ||
        msg === "timeout" ||
        msg.includes("noCurrent") ||
        msg.includes("Current ledger is unavailable") ||
        msg.includes("InsufficientNetworkMode") ||
        msg.includes("Not synced to the network") ||
        msg.includes("socket disconnected") ||
        msg.includes("ECONNRESET")
      ) {
        await new Promise((r) => setTimeout(r, 800 * (i + 1)));
        continue;
      }
      throw e;
    }
  }
  throw last;
}

function extractExports(wasmBytes) {
  let offset = 0;
  if (wasmBytes.readUInt32LE(0) !== 0x6d736100) {
    throw new Error("invalid wasm magic");
  }
  offset += 8;
  const names = [];
  function readVarUInt32() {
    let result = 0;
    let shift = 0;
    while (true) {
      const byte = wasmBytes[offset++];
      result |= (byte & 0x7f) << shift;
      if ((byte & 0x80) === 0) break;
      shift += 7;
    }
    return result;
  }
  while (offset < wasmBytes.length) {
    const id = wasmBytes[offset++];
    const size = readVarUInt32();
    const end = offset + size;
    if (id === 7) {
      const count = readVarUInt32();
      for (let i = 0; i < count; i++) {
        const nlen = readVarUInt32();
        const name = wasmBytes.toString("utf8", offset, offset + nlen);
        offset += nlen;
        const kind = wasmBytes[offset++];
        readVarUInt32();
        if (kind === 0) names.push(name);
      }
    }
    offset = end;
  }
  return names;
}

function createdContractAccount(meta) {
  for (const n of (meta && meta.AffectedNodes) || []) {
    const created = n.CreatedNode;
    if (created && created.LedgerEntryType === "Contract") {
      return (created.NewFields || {}).ContractAccount;
    }
    if (created && created.LedgerEntryType === "AccountRoot" && (created.NewFields || {}).ContractID) {
      return (created.NewFields || {}).Account;
    }
  }
  return null;
}

async function maybeAccept(url) {
  try {
    await rpc(url, "ledger_accept", {});
  } catch (_) {}
}

async function waitTx(url, hash) {
  await maybeAccept(url);
  for (let i = 0; i < 40; i++) {
    try {
      const tx = await rpcRetry(url, "tx", { transaction: hash });
      if (tx.validated || tx.meta) return tx;
    } catch (_) {}
    await maybeAccept(url);
    await new Promise((r) => setTimeout(r, 250));
  }
  throw new Error("tx " + hash + " not validated in 40s");
}

async function loadServerDefs(url) {
  const raw = await rpcRetry(url, "server_definitions", {});
  const names = new Set();
  for (const item of raw.FIELDS || []) {
    if (Array.isArray(item) && item[0]) names.add(item[0]);
  }
  return { raw, names, defs: loadDefinitions(raw) };
}

function loadDefinitions(raw) {
  const { codec } = loadXrpl();
  const copy = { ...raw };
  delete copy.status;
  delete copy.hash;
  return new codec.XrplDefinitions(copy);
}

async function signTx(url, secret, txJson, defs) {
  // Prefer node sign: 3.3.0 currently temBAD_SIGNATURE on locally signed
  // InstanceParameterValues too. Fall back to codec if node cannot encode
  // ParameterType (2.6.1).
  try {
    return await rpcRetry(url, "sign", { secret, tx_json: txJson });
  } catch (e) {
    const msg = String(e.message || e);
    if (!defs || (!msg.includes("ParameterType") && !msg.includes("contents did not meet"))) {
      throw e;
    }
    const { xrpl, codec, keypairs } = loadXrpl();
    const wallet = xrpl.Wallet.fromSeed(secret, { algorithm: "secp256k1" });
    const toSign = { ...txJson, SigningPubKey: wallet.publicKey };
    const signing = codec.encodeForSigning(toSign, defs);
    const sig = keypairs.sign(signing, wallet.privateKey);
    const blob = codec.encode({ ...toSign, TxnSignature: sig }, defs);
    return { tx_blob: blob, tx_json: { ...toSign, hash: null } };
  }
}

async function submitBlob(url, blob) {
  return rpcRetry(url, "submit", { tx_blob: blob });
}

function hexName(name) {
  return Buffer.from(name).toString("hex").toUpperCase();
}

async function main() {
  const cmd = process.argv[2];
  const cfg = JSON.parse(fs.readFileSync(process.argv[3], "utf8"));
  const url = cfg.rpc_url || "https://alphanet.xrpl.org";
  const info0 = await rpcRetry(url, "server_info", {});
  const networkId = cfg.network_id || info0.info.network_id || 21337;
  const serverDefs = await loadServerDefs(url);
  const fields = serverDefs.names;
  const defs = serverDefs.defs;
  const secret = cfg.wallet_seed;
  const algorithm = cfg.algorithm || "secp256k1";

  if (cmd === "info") {
    const info = await rpcRetry(url, "server_info", {});
    const feat = await rpcRetry(url, "feature", {});
    let smart = false;
    for (const v of Object.values(feat.features || {})) {
      if (v && v.name === "SmartContract") smart = !!v.enabled;
    }
    process.stdout.write(
      JSON.stringify({
        network_id: info.info.network_id,
        server_state: info.info.server_state,
        smart_contract: smart,
        build_version: info.info.build_version,
      }) + "\n"
    );
    return;
  }

  if (cmd === "deploy") {
    const wasm = fs.readFileSync(cfg.wasm_path);
    const exports = extractExports(wasm).filter((n) => n !== "memory");
    const { xrpl } = loadXrpl();
    const wallet = xrpl.Wallet.fromSeed(secret, { algorithm });
    const info = await rpcRetry(url, "account_info", {
      account: wallet.address,
      ledger_index: "current",
    });
    const seq = info.account_data.Sequence;

    const paramCounts = cfg.function_params || {};
    const Functions = exports.map((name) => {
      const fn = { Function: { FunctionName: hexName(name) } };
      const n = Number(paramCounts[name] || 0);
      // Create ABI must list ParameterType for every ContractCall value.
      // Calling with Parameters against an empty ABI crashes 2.6.1 (SIGSEGV)
      // and knocks 3.3.0 off the current ledger.
      if (n > 0) {
        fn.Function.Parameters = Array.from({ length: n }, () => ({
          Parameter: {
            ParameterFlag: 0,
            ParameterType: { type: "UINT64" },
          },
        }));
      }
      return fn;
    });
    const txJson = {
      TransactionType: "ContractCreate",
      Account: wallet.address,
      Fee: cfg.fee || "100000000",
      Sequence: seq,
      NetworkID: networkId,
      ContractCode: wasm.toString("hex").toUpperCase(),
      Functions,
    };
    // tfSendAmount = 0x00010000. Ordinary Payment to a ContractAccount is
    // tecNO_PERMISSION. Create-time values fund the pseudo-account.
    // Public 3.3.0: both arrays, ParameterType {type:AMOUNT}. First install
    // of a wasm hash only; reinstall against an empty-ABI source is temMALFORMED.
    // Local 2.6.1: node `sign` cannot encode ParameterType; values-only works.
    if (cfg.send_amount_drops) {
      const drops = String(cfg.send_amount_drops);
      const value = {
        InstanceParameterValue: {
          ParameterFlag: 65536,
          ParameterValue: { type: "AMOUNT", value: drops },
        },
      };
      txJson.InstanceParameterValues = [value];
      // 3.3.0 has Gas and can sign ParameterType. 2.6.1 has
      // ComputationAllowance; its sign rejects ParameterType.
      if (fields.has("Gas")) {
        txJson.InstanceParameters = [
          {
            InstanceParameter: {
              ParameterFlag: 65536,
              ParameterType: { type: "AMOUNT" },
            },
          },
        ];
      }
    }
    const signed = await signTx(url, secret, txJson, defs);
    const submitted = await submitBlob(url, signed.tx_blob);
    if (submitted.engine_result !== "tesSUCCESS") {
      throw new Error(submitted.engine_result + " " + (submitted.engine_result_message || ""));
    }
    const hash = submitted.tx_json.hash;
    const tx = await waitTx(url, hash);
    const contract = createdContractAccount(tx.meta);
    let contractBalance = null;
    if (contract) {
      try {
        const cinfo = await rpcRetry(url, "account_info", {
          account: contract,
          ledger_index: "validated",
        });
        contractBalance = (cinfo.account_data || {}).Balance || null;
      } catch (_) {}
    }
    process.stdout.write(
      JSON.stringify({
        success: true,
        txHash: hash,
        result: (tx.meta || {}).TransactionResult,
        contractAccount: contract,
        contractBalance,
        walletAddress: wallet.address,
        exports,
      }) + "\n"
    );
    return;
  }

  if (cmd === "call") {
    const { xrpl } = loadXrpl();
    const wallet = xrpl.Wallet.fromSeed(secret, { algorithm });
    const seq = (
      await rpcRetry(url, "account_info", {
        account: wallet.address,
        ledger_index: "current",
      })
    ).account_data.Sequence;
    const txJson = {
      TransactionType: "ContractCall",
      Account: wallet.address,
      ContractAccount: cfg.contract_account,
      FunctionName: hexName(cfg.function_name),
      Fee: cfg.fee || "1000000",
      Sequence: seq,
      NetworkID: networkId,
    };
    // Public 3.3.0-rc1 uses Gas; transia/alphanet 2.6.1-rc1 uses ComputationAllowance.
    const allowance = parseInt(cfg.gas || cfg.computation_allowance || "1000000", 10);
    if (fields.has("Gas")) txJson.Gas = allowance;
    else if (fields.has("ComputationAllowance")) txJson.ComputationAllowance = allowance;
    if (cfg.parameters && cfg.parameters.length) {
      txJson.Parameters = cfg.parameters.map((p) => {
        const n = BigInt(typeof p === "string" && p.startsWith("0x") ? p : String(p));
        return {
          Parameter: {
            ParameterFlag: 0,
            ParameterValue: {
              type: "UINT64",
              value: n.toString(16).toUpperCase().padStart(16, "0"),
            },
          },
        };
      });
    }
    const signed = await signTx(url, secret, txJson, defs);
    const submitted = await submitBlob(url, signed.tx_blob);
    const hash = submitted.tx_json && submitted.tx_json.hash;
    const applied =
      submitted.engine_result === "tesSUCCESS" ||
      (submitted.engine_result && String(submitted.engine_result).startsWith("tec"));
    let tx = { meta: {} };
    if (hash && applied) {
      try {
        tx = await waitTx(url, hash);
      } catch (_) {}
    }
    const meta = tx.meta || {};
    process.stdout.write(
      JSON.stringify({
        success: meta.TransactionResult === "tesSUCCESS",
        engine_result: submitted.engine_result,
        engine_result_message: submitted.engine_result_message || null,
        txHash: hash || null,
        result: meta.TransactionResult || submitted.engine_result,
        vmReturnCode: meta.VMReturnCode ?? meta.WasmReturnCode ?? null,
        gasUsed: meta.GasUsed ?? null,
      }) + "\n"
    );
    if (meta.TransactionResult !== "tesSUCCESS") process.exit(1);
    return;
  }

  if (cmd === "slot") {
    const objs = await rpcRetry(url, "account_objects", {
      account: cfg.owner,
      ledger_index: "validated",
    });
    const key = cfg.key || "value";
    for (const obj of objs.account_objects || []) {
      if (obj.LedgerEntryType !== "ContractData") continue;
      if (obj.ContractAccount !== cfg.contract_account) continue;
      const json = obj.ContractJson || {};
      function lookup(obj, k) {
        if (obj == null || typeof obj !== "object") return undefined;
        if (obj[k] !== undefined) return obj[k];
        const hx = Buffer.from(k).toString("hex");
        if (obj[hx] !== undefined) return obj[hx];
        if (obj[hx.toLowerCase()] !== undefined) return obj[hx.toLowerCase()];
        if (obj[hx.toUpperCase()] !== undefined) return obj[hx.toUpperCase()];
        return undefined;
      }
      let raw = lookup(json, key);
      if (raw === undefined && key.includes("_") && !/^[0-9]/.test(key.split("_")[1] || "")) {
        const parts = key.split("_");
        raw = lookup(json, parts[0]);
        if (raw && typeof raw === "object") raw = lookup(raw, parts.slice(1).join("_"));
      }
      if (raw === undefined) {
        process.stdout.write("0\n");
        return;
      }
      const s = String(raw).trim().toLowerCase().replace(/^0x/, "");
      process.stdout.write(String(s ? BigInt("0x" + s).toString(10) : 0) + "\n");
      return;
    }
    throw new Error("missing ContractData for " + cfg.contract_account);
  }

  if (cmd === "pay") {
    const { xrpl } = loadXrpl();
    const wallet = xrpl.Wallet.fromSeed(secret, { algorithm });
    const dest = cfg.destination;
    const drops = String(cfg.drops || "20000000");
    if (!dest) throw new Error("pay wants destination");
    const seq = (
      await rpcRetry(url, "account_info", {
        account: wallet.address,
        ledger_index: "current",
      })
    ).account_data.Sequence;
    const txJson = {
      TransactionType: "Payment",
      Account: wallet.address,
      Destination: dest,
      Amount: drops,
      Fee: cfg.fee || "12",
      Sequence: seq,
      NetworkID: networkId,
    };
    const signed = await signTx(url, secret, txJson, defs);
    const submitted = await submitBlob(url, signed.tx_blob);
    if (submitted.engine_result !== "tesSUCCESS") {
      throw new Error(submitted.engine_result + " " + (submitted.engine_result_message || ""));
    }
    const hash = submitted.tx_json.hash;
    const tx = await waitTx(url, hash);
    process.stdout.write(
      JSON.stringify({
        success: true,
        txHash: hash,
        result: (tx.meta || {}).TransactionResult,
        destination: dest,
        drops,
      }) + "\n"
    );
    return;
  }

  if (cmd === "balance") {
    const account = cfg.account;
    if (!account) throw new Error("balance wants account");
    const info = await rpcRetry(url, "account_info", {
      account,
      ledger_index: "validated",
    });
    process.stdout.write(String((info.account_data || {}).Balance || "0") + "\n");
    return;
  }

  throw new Error("unknown command " + cmd);
}

main().catch((err) => {
  process.stderr.write(String(err && err.stack ? err.stack : err) + "\n");
  process.exit(1);
});
