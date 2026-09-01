#!/usr/bin/env bash
# NEAR engineering gate: emit every registered near program to WAT/wasm,
# then assert the wasm import table is env and required exports exist.
# Does NOT start near-sandbox / nearcore / testnet.
set -euo pipefail
cd "$(dirname "$0")/../.."

OUT=${OUT:-build/near}
lake exe pf -- build --target near --out "$OUT"

python3 - "$OUT" <<'PY'
import sys
from pathlib import Path

out = Path(sys.argv[1])
wats = sorted(out.glob("*.wat"))
wasms = sorted(out.glob("*.wasm"))
if not wats:
    sys.exit("near check: no .wat produced")
if len(wats) != len(wasms):
    sys.exit(f"near check: wat/wasm count mismatch {len(wats)}/{len(wasms)}")

need_imports = (
    '(import "env" "input"',
    '(import "env" "storage_read"',
    '(import "env" "storage_write"',
    '(import "env" "storage_remove"',
    '(import "env" "storage_has_key"',
    '(import "env" "value_return"',
)
need_exports = (
    '(func (export "initialize")',
    '(func (export "get")',
)
counter_exports = (
    '(func (export "increment")',
)
ctx_imports = (
    '(import "env" "block_index"',
    '(import "env" "block_timestamp"',
    '(import "env" "predecessor_account_id"',
    '(import "env" "attached_deposit"',
    '(import "env" "account_balance"',
    '(import "env" "current_account_id"',
    '(import "env" "log_utf8"',
)
ctx_exports = (
    '(func (export "height")',
    '(func (export "seconds")',
    '(func (export "selfBal")',
    '(func (export "selfBalHigh")',
    '(func (export "takeDeposit")',
    '(func (export "takeDepositHigh")',
    '(func (export "takeDepositLegacy")',
    '(func (export "logReady")',
    '(func (export "logView")',
    '(func (export "selfId")',
    '(func (export "selfIdLength")',
    '(func (export "selfIdWord1")',
    '(func (export "checkSelfCall")',
)
bytes_anchors = (
    '(func $pf_utf8_valid',
    '(func (export "inspectBytes")',
    '(func (export "inspectString")',
    '(func (export "logString")',
    '(import "env" "log_utf8"',
    '(call $pf_log_utf8 (local.get $pf_r0) (local.get $pf_r1))',
    '(call $pf_utf8_valid (i32.const 260)',
    '(func (export "eventString")',
    '(func (export "eventEscapedMetadata")',
    '(call $pf_arena_alloc (i64.const 135) (i64.const 1))',
    '(i64.const 117)',
)
ft_event_anchors = (
    '(func $pf_json_escape_byte',
    '(func $pf_u128_decimal',
    '(local.set $bit (i64.const 128))',
    '(call $pf_arena_alloc (i64.const 528) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 938) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 634) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 1044) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 39) (i64.const 1))',
    '(func (export "mintZero")',
    '(func (export "mintTwo64")',
    '(func (export "mintTwo64PlusOne")',
    '(func (export "mintMax")',
    '(func (export "transferMax")',
    '(func (export "burnTwo64")',
    '(func (export "mintMemo")',
    '(func (export "transferMemo")',
    '(func (export "burnMemo")',
)
token_arithmetic_anchors = (
    '(func (export "addCarryOk")',
    '(func (export "addOverflowOk")',
    '(func (export "subBorrowOk")',
    '(func (export "subUnderflowOk")',
    '(func (export "mulFactorZeroOk")',
    '(func (export "mulU64SquareW1")',
    '(func (export "mulCarryOverflowOk")',
    '(func (export "mulCarryBoundaryW1")',
    '(func $pf_mul64_lo',
    '(func $pf_mul64_hi',
    '(call $pf_mul64_lo',
    '(call $pf_mul64_hi',
    'i64.add',
    'i64.sub',
    'i64.lt_u',
    'i64.gt_u',
    'i64.ge_u',
    'i64.extend_i32_u',
)
token_storage_anchors = (
    '(func (export "readW0")',
    '(func (export "readW1")',
    '(func (export "putMixed")',
    '(func (export "putShort")',
    '(func (export "putOversized")',
    '(func (export "remove")',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    '(i64.const 16)',
    'i64.shl',
    'i64.or',
)
memory_anchors = (
    '(func $pf_arena_reset',
    '(func $pf_arena_alloc',
    'memory.grow',
    '(func $pf_buffer64_begin',
    '(func $pf_buffer64_get',
    '(func (export "roundTrip")',
    '(func (export "growAndReuse")',
)
output_anchors = (
    '(local $pf_output_ptr i32)',
    '(local $pf_output_length i64)',
    '(call $pf_arena_alloc',
    '(func $pf_u128_decimal',
    '(call $pf_arena_alloc (i64.const 41) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 39) (i64.const 1))',
    '(func (export "jsonU128Zero")',
    '(func (export "jsonU128Two64")',
    '(func (export "jsonU128Two64PlusOne")',
    '(func (export "jsonU128Asymmetric")',
    '(func (export "jsonU128Max")',
    '(func (export "staticBytes")',
    '(func (export "staticString")',
    '(func (export "staticValues")',
    '(func (export "echoBytes")',
    '(call $pf_value_return (i64.add (i64.const 4)',
)
storage_balance_output_anchors = (
    '(func $pf_u128_decimal',
    '(local $pf_output_second_length i64)',
    '(call $pf_arena_alloc (i64.const 105) (i64.const 1))',
    '(func (export "none")',
    '(func (export "someZero")',
    '(func (export "someAsymmetric")',
    '(func (export "someMax")',
    '(func (export "malformedPresence")',
    '(func (export "malformedPresenceMax")',
    '(i64.const 2480464647488283259)',
    '(i64.const 7811882189714500642)',
)
storage_balance_bounds_output_anchors = (
    '(func $pf_u128_decimal',
    '(local $pf_output_second_length i64)',
    '(call $pf_arena_alloc (i64.const 97) (i64.const 1))',
    '(func (export "noMaxZero")',
    '(func (export "noMaxTwo64")',
    '(func (export "someAsymmetric")',
    '(func (export "someMax")',
    '(func (export "malformedPresence")',
    '(func (export "malformedPresenceMax")',
    '(i64.const 2466321603549274747)',
    '(i64.const 4189042963246099490)',
)
json_account_input_anchors = (
    '(func $pf_json_account_id',
    '(func $pf_json_account_key',
    '(func $pf_json_account_hex',
    '(i64.const 433)',
    '(i32.const 32)',
    '(func (export "accountLength")',
    '(func (export "accountW0")',
    '(func (export "accountW7")',
    '(call $pf_json_account_id (local.get $pf_input_ptr)',
)
json_amount_input_anchors = (
    '(func $pf_json_u128_amount',
    '(func $pf_json_u128_string',
    '(func $pf_json_amount_hex',
    '(i64.const 279)',
    '(func (export "amountW0")',
    '(func (export "amountW1")',
    '(func (export "commitW1")',
    '(call $pf_json_u128_amount (local.get $pf_input_ptr)',
)
json_memo_input_anchors = (
    '(func $pf_json_optional_memo16',
    '(func $pf_json_memo_string',
    '(func $pf_json_memo_put_cp',
    '(i64.const 139)',
    '(func (export "memoPresent")',
    '(func (export "memoLength")',
    '(func (export "memoW0")',
    '(func (export "memoW1")',
)
json_message_input_anchors = (
    '(func $pf_json_message64',
    '(func $pf_json_memo_string',
    '(func $pf_json_memo_put_cp',
    '(i64.const 426)',
    '(call $pf_arena_alloc (i64.const 72) (i64.const 8))',
    '(func (export "messageLength")',
    '(func (export "messageW0")',
    '(func (export "messageW7")',
)
json_ft_transfer_input_anchors = (
    '(func $pf_json_ft_transfer_args',
    '(func $pf_json_ft_key',
    '(func $pf_json_account_string',
    '(func $pf_json_u128_string',
    '(func $pf_json_memo_string',
    '(i64.const 786)',
    '(func (export "inspectReceiverLength")',
    '(func (export "inspectAmountW1")',
    '(func (export "inspectMemoPresent")',
)
json_ft_transfer_call_input_anchors = (
    '(func $pf_json_ft_transfer_call_args',
    '(func $pf_json_ft_transfer_call_key',
    '(func $pf_json_account_string',
    '(func $pf_json_u128_string',
    '(func $pf_json_memo_string',
    '(i64.const 1179)',
    '(call $pf_arena_alloc (i64.const 192) (i64.const 8))',
    '(func (export "receiverLength")',
    '(func (export "messageW7")',
)
json_ft_on_transfer_input_anchors = (
    '(func $pf_json_ft_on_transfer_args',
    '(func $pf_json_ft_on_transfer_key',
    '(func $pf_json_account_string',
    '(func $pf_json_u128_string',
    '(func $pf_json_memo_string',
    '(i64.const 1071)',
    '(call $pf_arena_alloc (i64.const 160) (i64.const 8))',
    '(func (export "senderLength")',
    '(func (export "messageW7")',
    '(func (export "commitAmountHigh")',
)
ft_receiver_value_anchors = (
    '(func (export "ft_on_transfer")',
    '(func $pf_json_ft_on_transfer_args',
    '(func $pf_u128_decimal',
    '(i64.const 1071)',
    '(call $pf_attached_deposit',
    '(call $pf_storage_write',
    '(call $pf_value_return',
)
promise_or_value_anchors = (
    '(func (export "choose")',
    '(func $pf_u128_decimal',
    '(call $pf_promise_batch_create',
    '(call $pf_promise_batch_action_function_call',
    '(call $pf_promise_return',
    '(call $pf_value_return',
)
ft_receiver_dual_anchors = (
    '(func (export "ft_on_transfer")',
    '(func $pf_json_ft_on_transfer_args',
    '(func $pf_u128_decimal',
    '(call $pf_promise_batch_create',
    '(call $pf_promise_batch_action_function_call',
    '(call $pf_promise_return',
    '(call $pf_value_return',
)
json_unit_output_anchors = (
    '(func (export "setMarker")',
    '(func (export "setMarkerVoid")',
    '(call $pf_arena_alloc (i64.const 4) (i64.const 1))',
    '(i32.store (local.get $pf_output_ptr) (i32.const 1819047278))',
    '(call $pf_value_return (i64.const 4)',
)
json_u128_mutation_anchors = (
    '(func (export "commitAsymmetric")',
    '(func (export "right")',
    '(func $pf_u128_decimal',
    '(call $pf_arena_alloc (i64.const 41) (i64.const 1))',
    '(call $pf_value_return',
    '(call $pf_storage_write',
)
json_ft_resolve_input_anchors = (
    '(func $pf_json_ft_resolve_args',
    '(func $pf_json_ft_resolve_key',
    '(func $pf_json_account_string',
    '(func $pf_json_u128_string',
    '(i64.const 1079)',
    '(call $pf_arena_alloc (i64.const 160) (i64.const 8))',
    '(func (export "senderLength")',
    '(func (export "receiverLength")',
    '(func (export "commitAmountHigh")',
)
storage_anchors = (
    '(global $pf_storage_result_status (mut i64)',
    '(func $pf_storage_result_byte',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    '(call $pf_storage_has_key',
    '(func (export "put")',
    '(func (export "readByte")',
    '(func (export "staleByteAfterMiss")',
    '(func (export "readSmallFits")',
    '(func (export "remove")',
    '(func (export "has")',
    '(func (export "putMaximumKey")',
    '(func (export "readMaximumKeyByte")',
    '(func (export "removeMaximumKey")',
    '(call $pf_arena_alloc (i64.const 72) (i64.const 1))',
)
storage_economics_anchors = (
    '(import "env" "storage_usage" (func $pf_storage_usage (result i64)))',
    '(func (export "usage")',
    '(func (export "insertShort4")',
    '(func (export "replaceShort4")',
    '(func (export "growShort8")',
    '(func (export "removeShort")',
    '(func (export "removeMissing")',
    '(func (export "insertLong4")',
    '(func (export "removeLong")',
    '(call $pf_storage_usage)',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
)
storage_registration_anchors = (
    '(func (export "storage_deposit")',
    '(func (export "registerCaller")',
    '(func (export "unregisterCaller")',
    '(func (export "forceUnregisterCaller")',
    '(func (export "probeCaller")',
    '(func (export "seedCallerMalformed8")',
    '(func (export "seedCallerZero")',
    '(func (export "seedCallerOne")',
    '(func (export "fixtureSetCostMax")',
    '(func (export "fixtureSetCostAddOverflow")',
    '(func (export "fixtureSeedCallerMixedSupply")',
    '(func (export "fixtureSeedCallerMaxSupply")',
    '(func (export "totalSupplyW0")',
    '(func (export "totalSupplyW1")',
    '(import "env" "storage_usage" (func $pf_storage_usage (result i64)))',
    '(import "env" "attached_deposit"',
    '(import "env" "predecessor_account_id"',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    '(call $pf_storage_usage)',
    '(call $pf_promise_batch_create',
    '(call $pf_promise_batch_action_transfer',
    '(call $pf_mul64_lo',
    '(call $pf_mul64_hi',
    '(func $pf_json_storage_deposit_args',
    '(func $pf_u128_decimal',
    '(call $pf_arena_alloc (i64.const 459) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 105) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 72) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 16) (i64.const 8))',
)
json_storage_deposit_input_anchors = (
    '(func $pf_json_storage_deposit_args',
    '(func $pf_json_storage_deposit_key',
    '(func $pf_json_account_string',
    '(call $pf_arena_alloc (i64.const 459) (i64.const 1))',
    '(call $pf_arena_alloc (i64.const 88) (i64.const 8))',
    '(func (export "inspectAccountPresent")',
    '(func (export "commitRegistrationOnly")',
)
vector_anchors = (
    '(func (export "push")',
    '(func (export "setFirst")',
    '(func (export "pop")',
    '(func (export "getAt")',
    '(local $pf_v0 i64)',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    '(call $pf_storage_read',
    'i64.and',
    'i64.shr_u',
    'i64.shl',
    'i64.or',
)
lookup_anchors = (
    '(func (export "mapGet")',
    '(func (export "mapHas")',
    '(func (export "mapPut")',
    '(func (export "mapRemove")',
    '(func (export "setHas")',
    '(func (export "setInsert")',
    '(func (export "setRemove")',
    '(func (export "tokenPutSelfMixed")',
    '(func (export "tokenPutCallerMax")',
    '(func (export "tokenPutShortFixture")',
    '(func (export "tokenSeedSelfMalformed8")',
    '(func (export "tokenSeedSelfMalformed20")',
    '(call $pf_arena_alloc (i64.const 72) (i64.const 1))',
    '(i64.const 16)',
    '(i64.const 20)',
    '(call $pf_storage_has_key',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    'i64.and',
    'i64.shr_u',
    'i64.shl',
    'i64.or',
)
ledger_anchors = (
    '(func (export "ft_balance_of")',
    '(func (export "ft_total_supply")',
    '(func (export "ft_transfer")',
    '(func (export "mintSelfOne")',
    '(func (export "mintSelfTwo64")',
    '(func (export "mintSelfMax")',
    '(func (export "burnSelfOne")',
    '(func (export "burnSelfMax")',
    '(func (export "transferCallerToSelfOne")',
    '(func (export "transferCallerToSelfZero")',
    '(func (export "seedSelfMalformed8")',
    '(func (export "seedSelfMalformed20")',
    '(func (export "fixtureSetSupplyMax")',
    '(func $pf_json_account_id',
    '(func $pf_json_ft_transfer_args',
    '(func $pf_storage_result_near_token_strict',
    '(func $pf_u128_decimal',
    '(call $pf_arena_alloc (i64.const 72) (i64.const 1))',
    '(call $pf_input',
    '(call $pf_value_return',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    'i64.add',
    'i64.sub',
    'i64.lt_u',
    'i64.ge_u',
)
queue_anchors = (
    '(func (export "push")',
    '(func (export "pop")',
    '(func (export "getAt")',
    '(func (export "hasAt")',
    '(func (export "peek")',
    '(func (export "getHead")',
    '(call $pf_storage_has_key',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    'i64.lt_u',
    'i64.sub',
)
iterable_anchors = (
    '(func (export "mapPut")',
    '(func (export "mapRemove")',
    '(func (export "mapIndex")',
    '(func (export "mapKeyAt")',
    '(func (export "setInsert")',
    '(func (export "setRemove")',
    '(func (export "setIndex")',
    '(func (export "setKeyAt")',
    '(call $pf_storage_has_key',
    '(call $pf_storage_read',
    '(call $pf_storage_write',
    '(call $pf_storage_remove',
    'i64.lt_u',
    'i64.shl',
    'i64.or',
)
promise_anchors = (
    '(func (export "send")',
    '(func (export "sendMissing")',
    '(func (export "sendReturned")',
    '(func (export "sendReturnedMissing")',
    '(func (export "sendThenSuccess")',
    '(func (export "sendThenMissing")',
    '(func (export "sendThenOversized")',
    '(func (export "callbackQuotedU128")',
    '(func (export "decodeJsonMax")',
    '(func (export "transferCallerDetached")',
    '(func (export "transferCallerReturned")',
    '(func (export "transferSelfDetached")',
    '(func (export "transferShortDetached")',
    '(func (export "transferPaddedDetached")',
    '(func (export "transferMaxAccountReturned")',
    '(func (export "inspectFtOnTransfer")',
    '(import "env" "promise_batch_create"',
    '(import "env" "promise_batch_then"',
    '(import "env" "promise_batch_action_function_call"',
    '(import "env" "promise_batch_action_function_call_weight"',
    '(import "env" "promise_return"',
    '(import "env" "current_account_id"',
    '(call $pf_promise_batch_create',
    '(call $pf_promise_batch_action_function_call',
    '(call $pf_promise_batch_action_function_call_weight',
    '(call $pf_promise_batch_then',
    '(call $pf_promise_return',
    '(func $pf_promise_result_quoted_u128',
    '(i64.const 11068046444225730969)',
    '(call $pf_arena_alloc (local.get $pf_r0) (i64.const 1))',
    '(if (i64.lt_u (i64.const 63) (local.get $pf_r0))',
    '(call $pf_arena_alloc (i64.const 16) (i64.const 8))',
    '(call $pf_arena_alloc (i64.const 844) (i64.const 1))',
    '(i64.const 20000000000000)',
)
promise_result_anchors = (
    '(func (export "resultsCount")',
    '(func (export "resultStatus")',
    '(func (export "resultLength")',
    '(func (export "resultFits")',
    '(func (export "resultByte")',
    '(import "env" "promise_results_count"',
    '(import "env" "promise_result"',
    '(global $pf_promise_result_status (mut i64)',
    '(func $pf_promise_result_byte',
    '(call $pf_promise_results_count',
    '(call $pf_promise_result',
    '(call $pf_register_len (i64.const 4)',
    '(call $pf_read_register (i64.const 4)',
)
migration_anchors = (
    '(func (export "migrate")',
    '(func (export "revisionOf")',
    '(import "env" "predecessor_account_id"',
    '(import "env" "current_account_id"',
    '(i64.const 10223451468950344877)',
    '(i64.const 11209400244185005294)',
    '(global.set $pf_storage_result_status (call $pf_storage_read',
    '(call $pf_storage_result_byte',
)
forbid = ("host_lib", "xrpl_wasm_std", "get_current_contract_call")

for wat in wats:
    text = wat.read_text(encoding="utf-8")
    extra = ()
    if wat.stem == "Counter":
        extra = counter_exports
    elif wat.stem == "NearCtx":
        extra = ctx_imports + ctx_exports
    elif wat.stem == "NearBytes":
        extra = bytes_anchors
    elif wat.stem == "NearFungibleTokenEvent":
        extra = ft_event_anchors
    elif wat.stem == "NearTokenArithmetic":
        extra = token_arithmetic_anchors
    elif wat.stem == "NearTokenStorage":
        extra = token_storage_anchors
    elif wat.stem == "NearMemory":
        extra = memory_anchors
    elif wat.stem == "NearOutput":
        extra = output_anchors
    elif wat.stem == "NearStorageBalanceOutput":
        extra = storage_balance_output_anchors
    elif wat.stem == "NearStorageBalanceBoundsOutput":
        extra = storage_balance_bounds_output_anchors
    elif wat.stem == "NearJsonAccountInput":
        extra = json_account_input_anchors
    elif wat.stem == "NearJsonAmountInput":
        extra = json_amount_input_anchors
    elif wat.stem == "NearJsonMemoInput":
        extra = json_memo_input_anchors
    elif wat.stem == "NearJsonMessageInput":
        extra = json_message_input_anchors
    elif wat.stem == "NearJsonFtTransferInput":
        extra = json_ft_transfer_input_anchors
    elif wat.stem == "NearJsonFtTransferCallInput":
        extra = json_ft_transfer_call_input_anchors
    elif wat.stem == "NearJsonFtOnTransferInput":
        extra = json_ft_on_transfer_input_anchors
    elif wat.stem == "NearFtReceiverValue":
        extra = ft_receiver_value_anchors
    elif wat.stem == "NearPromiseOrValue":
        extra = promise_or_value_anchors
    elif wat.stem == "NearFtReceiverDual":
        extra = ft_receiver_dual_anchors
    elif wat.stem == "NearJsonUnitOutput":
        extra = json_unit_output_anchors
    elif wat.stem == "NearJsonU128Mutation":
        extra = json_u128_mutation_anchors
    elif wat.stem == "NearJsonFtResolveInput":
        extra = json_ft_resolve_input_anchors
    elif wat.stem == "NearJsonStorageDepositInput":
        extra = json_storage_deposit_input_anchors
    elif wat.stem == "NearStorage":
        extra = storage_anchors
    elif wat.stem == "NearStorageEconomics":
        extra = storage_economics_anchors
    elif wat.stem == "NearStorageRegistration":
        extra = storage_registration_anchors
    elif wat.stem == "NearVector":
        extra = vector_anchors
    elif wat.stem == "NearLookup":
        extra = lookup_anchors
    elif wat.stem == "NearFungibleLedger":
        extra = ledger_anchors
    elif wat.stem == "NearQueue":
        extra = queue_anchors
    elif wat.stem == "NearIterable":
        extra = iterable_anchors
    elif wat.stem == "NearPromise":
        extra = promise_anchors
    elif wat.stem == "NearPromiseResult":
        extra = promise_result_anchors
    elif wat.stem == "NearMigration":
        extra = migration_anchors
    for needle in need_imports + need_exports + extra:
        if needle not in text:
            sys.exit(f"near check: {wat.name} missing {needle!r}")
    for needle in forbid:
        if needle in text:
            sys.exit(f"near check: {wat.name} still contains {needle!r}")
    wasm = out / f"{wat.stem}.wasm"
    if not wasm.is_file() or wasm.stat().st_size == 0:
        sys.exit(f"near check: missing wasm {wasm.name}")
    magic = wasm.read_bytes()[:4]
    if magic != b"\x00asm":
        sys.exit(f"near check: {wasm.name} is not wasm")
    print(f"near check ok: {wat.name} / {wasm.name}")
print("near engineering gate: ok")
PY
