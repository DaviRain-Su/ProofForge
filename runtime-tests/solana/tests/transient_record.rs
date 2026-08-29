//! Mollusk fixture for the fixed-width POD record SDK slice (`Examples.TransientLedger` and
//! `Examples.TransientOrderTape`). It pins, on the live sBPF path, that bounded fixed-width
//! records append, rewrite, count, truncate, pop, clear, and finish as whole records through the
//! existing two-slot `Vector64` component, that same-shape slots stay disjoint, that consumers
//! branch on the SDK record preflight, and that full/OOB/stale/OOM boundaries are explicit
//! terminal errors with the underlying component's vocabulary (0x1201 OOM, 0x1202 bounds,
//! 0x1203 state).

mod common;

use {
    common::{dummy_state_key, harness, instruction},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

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

fn ledger_setup() -> (Pubkey, Mollusk, Account) {
    let (program_id, mollusk) = harness("TransientLedger", "PF_TRANSIENT_LEDGER_SO");
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

#[test]
fn ledger_appends_whole_two_limb_records() {
    let (program_id, mollusk, state) = ledger_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "appendEntry",
        &[5, 6],
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
}

#[test]
fn ledger_rewrites_and_reads_record_aligned_limbs() {
    let (program_id, mollusk, state) = ledger_setup();
    for (index, expected) in [(0u64, 101777u64), (1, 202777)] {
        invoke(
            &mollusk,
            program_id,
            &state,
            "rewriteAmount",
            &[index, 777],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn ledger_truncate_and_pop_stay_record_aligned() {
    let (program_id, mollusk, state) = ledger_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "truncateLedger",
        &[1],
        &[Check::success(), Check::return_data(&111u64.to_le_bytes())],
    );
    invoke(&mollusk, program_id, &state, "dropTopEntry", &[], &[
        Check::success(),
        Check::return_data(&90002u64.to_le_bytes()),
    ]);
}

#[test]
fn ledger_rejects_whole_records_when_preflight_full() {
    let (program_id, mollusk, state) = ledger_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "rejectWhenFull",
        &[5, 6],
        &[Check::success(), Check::return_data(&999u64.to_le_bytes())],
    );
}

#[test]
fn ledger_slots_stay_disjoint_and_finish_isolates() {
    let (program_id, mollusk, state) = ledger_setup();
    for (index, expected) in [(0u64, 155022u64), (1, 104044)] {
        invoke(
            &mollusk,
            program_id,
            &state,
            "twinLedgers",
            &[index],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
    invoke(
        &mollusk,
        program_id,
        &state,
        "twinRewriteIsolated",
        &[],
        &[Check::success(), Check::return_data(&400811u64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        &state,
        "finishIsolation",
        &[],
        &[Check::success(), Check::return_data(&93u64.to_le_bytes())],
    );
}

#[test]
fn ledger_failure_matrix() {
    let (program_id, mollusk, state) = ledger_setup();
    // A record index inside the compile-time payload but at or above the live count.
    invoke(
        &mollusk,
        program_id,
        &state,
        "oobRecord",
        &[1],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
    // A limb index at or above the fixed stride never reads the next record's limb.
    invoke(&mollusk, program_id, &state, "oobLimb", &[], &[
        Check::err(ProgramError::Custom(0x1202)),
    ]);
    // `finish` invalidates the record handle without reclaiming the bump allocation.
    invoke(&mollusk, program_id, &state, "staleAfterFinish", &[], &[
        Check::err(ProgramError::Custom(0x1203)),
    ]);
    // A second-slot handle that was never begun stays inactive on its own state error.
    invoke(&mollusk, program_id, &state, "unbegunAlternate", &[], &[
        Check::err(ProgramError::Custom(0x1203)),
    ]);
}

#[test]
fn ledger_cross_slot_oom_is_explicit() {
    let (program_id, mollusk, state) = ledger_setup();
    invoke(&mollusk, program_id, &state, "crossSlotOom", &[], &[
        Check::err(ProgramError::Custom(0x1201)),
    ]);
}

fn tape_setup() -> (Pubkey, Mollusk, Account) {
    let (program_id, mollusk) = harness("TransientOrderTape", "PF_TRANSIENT_ORDER_TAPE_SO");
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

#[test]
fn tape_appends_whole_records_after_preflight() {
    let (program_id, mollusk, state) = tape_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "appendWithRoom",
        &[77, 88, 99],
        &[Check::success(), Check::return_data(&277u64.to_le_bytes())],
    );
}

#[test]
fn tape_clear_reuse_policy_rewrites_only_whole_records() {
    let (program_id, mollusk, state) = tape_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "appendOverwrite",
        &[7, 8, 9],
        &[Check::success(), Check::return_data(&90808u64.to_le_bytes())],
    );
}

#[test]
fn tape_reads_aligned_records_through_runtime_indexes() {
    let (program_id, mollusk, state) = tape_setup();
    for (index, expected) in [(0u64, 4563u64), (1, 5673u64)] {
        invoke(
            &mollusk,
            program_id,
            &state,
            "readQuote",
            &[index],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn tape_slots_are_disjoint_and_pop_is_record_aligned() {
    let (program_id, mollusk, state) = tape_setup();
    for (index, expected) in [(0u64, 67088u64), (1, 77058u64)] {
        invoke(
            &mollusk,
            program_id,
            &state,
            "twinTapes",
            &[index],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
    invoke(
        &mollusk,
        program_id,
        &state,
        "dropTopQuote",
        &[],
        &[Check::success(), Check::return_data(&8101u64.to_le_bytes())],
    );
}

#[test]
fn tape_finish_isolates_only_its_own_slot() {
    let (program_id, mollusk, state) = tape_setup();
    invoke(
        &mollusk,
        program_id,
        &state,
        "tapeFinishIsolated",
        &[],
        &[Check::success(), Check::return_data(&9u64.to_le_bytes())],
    );
}

#[test]
fn tape_failure_matrix() {
    let (program_id, mollusk, state) = tape_setup();
    // A limb index at or above the fixed stride terminates instead of reading the next record's
    // first limb.
    invoke(&mollusk, program_id, &state, "oobLimb", &[], &[
        Check::err(ProgramError::Custom(0x1202)),
    ]);
    // After a whole-record shortening, record 1 is inside the payload but past the live count.
    invoke(
        &mollusk,
        program_id,
        &state,
        "oobAfterRewind",
        &[1],
        &[Check::err(ProgramError::Custom(0x1202))],
    );
    invoke(&mollusk, program_id, &state, "staleAfterFinish", &[], &[
        Check::err(ProgramError::Custom(0x1203)),
    ]);
    invoke(&mollusk, program_id, &state, "unbegunAlternate", &[], &[
        Check::err(ProgramError::Custom(0x1203)),
    ]);
}

#[test]
fn tape_cross_slot_oom_is_explicit() {
    let (program_id, mollusk, state) = tape_setup();
    invoke(&mollusk, program_id, &state, "crossSlotOom", &[], &[
        Check::err(ProgramError::Custom(0x1201)),
    ]);
}
