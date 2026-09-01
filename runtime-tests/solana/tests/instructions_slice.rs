//! Mollusk ± coverage for svm-rt-004 bounded Instructions / fixed-offset sliced sysvar
//! (`Examples.InstructionsSlice`).
//!
//! Fixture layout (24 bytes), matching the compile-time geometry in Lean:
//! - `u16` `num_instructions` at offset 0
//! - marker `u64` at offset 8
//! - `u16` `current_index` at offset 16 (low half of word 2; trailing bytes pad to 24)
//!
//! Positive path: official Instructions sysvar key + full window.
//! Negative paths: short account and wrong key fail closed to sentinel `0`.

mod common;

use {
    common::{dummy_state_account, dummy_state_key, harness, instruction},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
};

const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const SERIALIZED_LEN: usize = 24;
const MARKER: u64 = 0x1122_3344_5566_7788;
const NUM_INSTRUCTIONS: u16 = 2;
const CURRENT_INDEX: u16 = 1;

/// Official Instructions sysvar: `Sysvar1nstructions1111111111111111111111111`.
fn instructions_sysvar_key() -> Pubkey {
    Pubkey::new_from_array([
        6, 167, 213, 23, 24, 123, 209, 102, 53, 218, 212, 4, 85, 253, 194, 192, 193, 36, 198,
        143, 33, 86, 117, 165, 219, 186, 203, 95, 8, 0, 0, 0,
    ])
}

/// Sysvar program owner: `Sysvar1111111111111111111111111111111111111`.
fn sysvar_owner() -> Pubkey {
    Pubkey::new_from_array([
        6, 167, 213, 23, 24, 117, 247, 41, 199, 61, 147, 64, 143, 33, 97, 32, 6, 126, 216, 140,
        118, 224, 140, 40, 127, 193, 148, 96, 0, 0, 0, 0,
    ])
}

fn instructions_fixture(num: u16, marker: u64, current: u16) -> Vec<u8> {
    let mut data = vec![0u8; SERIALIZED_LEN];
    data[0..2].copy_from_slice(&num.to_le_bytes());
    data[8..16].copy_from_slice(&marker.to_le_bytes());
    data[16..18].copy_from_slice(&current.to_le_bytes());
    data
}

fn instructions_account(data: Vec<u8>) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, data.len(), &sysvar_owner());
    account.data = data;
    account
}

fn plain_data_account(data: Vec<u8>) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, data.len(), &Pubkey::new_unique());
    account.data = data;
    account
}

fn call(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state_key: Pubkey,
    ix_key: Pubkey,
    ix_account: Account,
    name: &str,
    expected: u64,
) {
    let ix = instruction(
        program_id,
        state_key,
        name,
        &[],
        false,
        false,
        vec![AccountMeta::new_readonly(ix_key, false)],
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (state_key, dummy_state_account(&program_id)),
            (ix_key, ix_account),
        ],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
        ],
    );
}

#[test]
fn instructions_slice_positive_path() {
    let (program_id, mollusk) = harness("InstructionsSlice", "PF_INSTRUCTIONS_SLICE_SO");
    let state_key = dummy_state_key(&program_id);
    let ix_key = instructions_sysvar_key();
    let data = instructions_fixture(NUM_INSTRUCTIONS, MARKER, CURRENT_INDEX);
    let account = instructions_account(data);

    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "authenticated",
        1,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "fits",
        1,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "numInstructions",
        NUM_INSTRUCTIONS as u64,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "currentIndex",
        CURRENT_INDEX as u64,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "markerWord",
        MARKER,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account,
        "gatedNum",
        NUM_INSTRUCTIONS as u64,
    );
}

#[test]
fn instructions_slice_short_account_fail_closed() {
    let (program_id, mollusk) = harness("InstructionsSlice", "PF_INSTRUCTIONS_SLICE_SO");
    let state_key = dummy_state_key(&program_id);
    let ix_key = instructions_sysvar_key();
    let mut data = instructions_fixture(NUM_INSTRUCTIONS, MARKER, CURRENT_INDEX);
    data.truncate(4); // below compile-time 24-byte window
    let account = instructions_account(data);

    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "authenticated",
        1,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "fits",
        0,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "numInstructions",
        0,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "currentIndex",
        0,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "markerWord",
        0,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account,
        "gatedNum",
        0,
    );
}

#[test]
fn instructions_slice_wrong_key_fail_closed() {
    let (program_id, mollusk) = harness("InstructionsSlice", "PF_INSTRUCTIONS_SLICE_SO");
    let state_key = dummy_state_key(&program_id);
    let ix_key = Pubkey::new_unique();
    let data = instructions_fixture(NUM_INSTRUCTIONS, MARKER, CURRENT_INDEX);
    let account = plain_data_account(data);

    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "authenticated",
        0,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "fits",
        1,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account.clone(),
        "numInstructions",
        NUM_INSTRUCTIONS as u64,
    );
    call(
        &mollusk,
        program_id,
        state_key,
        ix_key,
        account,
        "gatedNum",
        0,
    );
}
