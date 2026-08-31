#!/usr/bin/env python3
"""Exercise both state-persisting terminals of the Promise-or-U128 target policy."""
import os
import sys
from pathlib import Path
from near_rpc import NearClient, NearRpcError

def req(name: str) -> str:
    value = os.environ.get(name, "")
    if not value: raise SystemExit(f"missing {name}")
    return value

def main() -> None:
    client = NearClient(req("PF_NEAR_RPC"), Path(req("PF_NEAR_HOME")))
    client.deploy(Path(req("PF_NEAR_POV_WASM")))
    initial_high = 0x123456789ABCDEF0
    client.call("initialize", NearClient.encode_u64_le(initial_high))
    value = 7
    immediate = client.call("choose", NearClient.encode_u64_le(value))
    expected = (initial_high << 64) | value
    actual = NearClient.success_value_bytes(immediate)
    if actual != f'"{expected}"'.encode():
        raise AssertionError(f"immediate branch lost asymmetric quoted-u128 bytes: {actual!r}")
    if client.view_u64("get") != value or client.view_u64("high") != 0x8877665544332211:
        raise AssertionError("immediate branch state fields were not independently persisted")

    client.create_subaccount_with_key("receiver.test.near", 10**27)
    client.deploy_to("receiver.test.near", Path(req("PF_NEAR_PROMISE_WASM")))
    client.call_on("receiver.test.near", "initialize", NearClient.encode_u64_le(0), signer="receiver.test.near")
    returned = client.call("choose", NearClient.encode_u64_le(0))
    if NearClient.success_value_bytes(returned) != NearClient.encode_u64_le(77):
        raise AssertionError("Promise branch did not forward the exact child result")
    if client.view_u64("get") != 9 or client.view_u64("high") != 0x1122334455667788:
        raise AssertionError("Promise branch did not persist both state fields before promise_return")
    print("near-promise-or-value: immediate quoted U128 and returned child terminals ok")

if __name__ == "__main__":
    try: main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-promise-or-value: FAIL: {exc}", file=sys.stderr); raise SystemExit(1)
