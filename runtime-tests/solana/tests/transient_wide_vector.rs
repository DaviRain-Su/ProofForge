//! Focused Mollusk matrix for allocation-free invocation-local typed UInt128/UInt256 vectors.
//! The artifacts exercise only the existing transient-vector component while pinning exact/full
//! boundaries, no-partial-push rejection, typed runtime indexes, stale handles, and shared-heap
//! two-slot isolation/OOM.

mod common;

use {
    common::{dummy_state_key, harness, instruction},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

fn wide128(words: [u64; 2]) -> Vec<u8> {
    words.into_iter().flat_map(u64::to_le_bytes).collect()
}

fn wide256(words: [u64; 4]) -> Vec<u8> {
    words.into_iter().flat_map(u64::to_le_bytes).collect()
}

fn setup(name: &str, env_name: &str) -> (Pubkey, Mollusk, Account) {
    let (program_id, mollusk) = harness(name, env_name);
    let state_key = dummy_state_key(&program_id);
    let init = instruction(
        program_id,
        state_key,
        "initialize",
        &[7],
        true,
        true,
        vec![],
    );
    let initialized = mollusk.process_and_validate_instruction(
        &init,
        &[(state_key, common::state_account(&program_id, 16))],
        &[Check::success()],
    );
    let state = initialized
        .resulting_accounts
        .iter()
        .find(|(key, _)| *key == state_key)
        .expect("state account")
        .1
        .clone();
    (program_id, mollusk, state)
}

fn invoke(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state: &Account,
    name: &str,
    params: &[u64],
    checks: &[Check],
) {
    let state_key = dummy_state_key(&program_id);
    let ix = instruction(program_id, state_key, name, params, true, false, vec![]);
    mollusk.process_and_validate_instruction(&ix, &[(state_key, state.clone())], checks);
}

#[test]
fn uint128_exact_boundary_and_reject_policy_preserve_typed_values() {
    let (program_id, mollusk, state) = setup("TransientWide128", "PF_TRANSIENT_WIDE128_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "pushExact",
        &[91, 92],
        &[Check::success(), Check::return_data(&wide128([91, 92]))],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "rejectAtFull",
        &[901, 902],
        &[Check::success(), Check::return_data(&wide128([31, 32]))],
    );
}

#[test]
fn uint128_full_push_rejects_before_a_partial_value() {
    let (program_id, mollusk, state) = setup("TransientWide128", "PF_TRANSIENT_WIDE128_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "overflowAtFull",
        &[91, 92],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
}

#[test]
fn uint128_runtime_set_get_drop_truncate_clear_and_oob_are_typed() {
    let (program_id, mollusk, state) = setup("TransientWide128", "PF_TRANSIENT_WIDE128_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "setAndGet",
        &[1, 71, 72],
        &[Check::success(), Check::return_data(&wide128([71, 72]))],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "rewindAndReuse",
        &[81, 82],
        &[Check::success(), Check::return_data(&wide128([9, 10]))],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "readAt",
        &[2],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
}

#[test]
fn uint128_two_slots_are_isolated_and_finish_is_stale() {
    let (program_id, mollusk, state) = setup("TransientWide128", "PF_TRANSIENT_WIDE128_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "twoSlotIsolation",
        &[],
        &[Check::success(), Check::return_data(&wide128([201, 202]))],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "staleAfterFinish",
        &[],
        &[Check::err(ProgramError::Custom(0x1203))],
    );
}

#[test]
fn uint256_exact_boundary_and_clear_policy_preserve_typed_values() {
    let (program_id, mollusk, state) = setup("TransientWide256", "PF_TRANSIENT_WIDE256_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "pushExact",
        &[91, 92, 93, 94],
        &[
            Check::success(),
            Check::return_data(&wide256([91, 92, 93, 94])),
        ],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "clearWhenFull",
        &[81, 82, 83, 84],
        &[
            Check::success(),
            Check::return_data(&wide256([81, 82, 83, 84])),
        ],
    );
}

#[test]
fn uint256_full_push_rejects_before_a_partial_value() {
    let (program_id, mollusk, state) = setup("TransientWide256", "PF_TRANSIENT_WIDE256_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "overflowAtFull",
        &[91, 92, 93, 94],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
}

#[test]
fn uint256_runtime_set_get_drop_truncate_and_oob_are_typed() {
    let (program_id, mollusk, state) = setup("TransientWide256", "PF_TRANSIENT_WIDE256_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "setAndGet",
        &[1, 71, 72, 73, 74],
        &[
            Check::success(),
            Check::return_data(&wide256([71, 72, 73, 74])),
        ],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "dropAndRewind",
        &[],
        &[
            Check::success(),
            Check::return_data(&wide256([17, 18, 19, 20])),
        ],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "readAt",
        &[1],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
}

#[test]
fn uint256_stale_and_cross_slot_oom_are_inherited() {
    let (program_id, mollusk, state) = setup("TransientWide256", "PF_TRANSIENT_WIDE256_SO");
    invoke(
        &mollusk,
        program_id,
        &state,
        "staleAfterFinish",
        &[],
        &[Check::err(ProgramError::Custom(0x1203))],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "crossSlotOom",
        &[],
        &[Check::err(ProgramError::Custom(0x1201))],
    );
}
