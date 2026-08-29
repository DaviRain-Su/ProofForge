//! Mollusk fixture for the dedicated same-kind transient multi-handle example
//! (`Examples.TransientPair`). It pins, on the live sBPF path, that two compile-time
//! `Vector64` handles and two compile-time `Bytes` handles run simultaneously with disjoint
//! metadata banks, disjoint payload regions, independent lengths/capacities, isolated
//! finish/clear/truncate/pop, explicit unbegun-slot/state failures, and explicit OOM through
//! the shared bounded downward bump heap.

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
    state: Account,
    name: &str,
    params: &[u64],
    checks: &[Check],
) -> mollusk_svm::result::InstructionResult {
    let state_key = dummy_state_key(&program_id);
    let ix = instruction(program_id, state_key, name, params, true, false, vec![]);
    mollusk.process_and_validate_instruction(&ix, &[(state_key, state)], checks)
}

fn setup() -> (Pubkey, Mollusk, Account) {
    let (program_id, mollusk) = harness("TransientPair", "PF_TRANSIENT_PAIR_SO");
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
fn same_kind_vector_slots_read_disjoint_payloads_at_runtime() {
    let (program_id, mollusk, state) = setup();
    for (index, expected) in [(0u64, 88u64), (1, 99)] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            "vectorPairSetGet",
            &[index],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn same_kind_vector_slot_clear_truncate_and_pop_are_isolated() {
    let (program_id, mollusk, state) = setup();
    let cases: [(&str, u64); 3] = [
        ("vectorPairClearIsolated", 20),
        ("vectorPairTruncateIsolated", 25),
        ("vectorPairPopIsolated", 42),
    ];
    for (name, expected) in cases {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            name,
            &[],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn same_kind_vector_slot_finish_keeps_the_other_slot_live() {
    let (program_id, mollusk, state) = setup();
    invoke(
        &mollusk,
        program_id,
        state,
        "vectorPairFinishIsolated",
        &[],
        &[Check::success(), Check::return_data(&66u64.to_le_bytes())],
    );
}

#[test]
fn all_four_transient_slots_share_one_invocation_heap() {
    let (program_id, mollusk, state) = setup();
    invoke(
        &mollusk,
        program_id,
        state,
        "fourTransientPairs",
        &[],
        &[Check::success(), Check::return_data(&26u64.to_le_bytes())],
    );
}

#[test]
fn same_kind_vector_slot_failure_matrix() {
    let (program_id, mollusk, state) = setup();
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        "vectorPairUnbegunSlot",
        &[],
        &[Check::err(ProgramError::Custom(0x1203))],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        "vectorPairOom",
        &[],
        &[Check::err(ProgramError::Custom(0x1201))],
    );
}

#[test]
fn same_kind_byte_slots_read_disjoint_payloads_at_runtime() {
    let (program_id, mollusk, state) = setup();
    for (index, expected) in [(0u64, 17425u64), (1, 17561)] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            "bytesPairSetGet",
            &[index],
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
    invoke(
        &mollusk,
        program_id,
        state,
        "bytesPairTruncateIsolated",
        &[],
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    );
}

#[test]
fn same_kind_byte_slot_failure_matrix() {
    let (program_id, mollusk, state) = setup();
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        "bytesPairUnbegunSlot",
        &[],
        &[Check::err(ProgramError::Custom(0x1213))],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        "bytesPairOom",
        &[],
        &[Check::err(ProgramError::Custom(0x1211))],
    );
}
