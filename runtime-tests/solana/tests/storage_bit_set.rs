mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

// Arbitrary named source errors currently share the SVM generic fail-closed code.
const OUT_OF_RANGE: u32 = 1;
const REPLAY: u32 = 1;
const SOURCE_STATE_LEN: usize = 2 * 8;
const FEATURE_STORAGE_LEN: usize = 4 * 8;
const CLAIM_STORAGE_LEN: usize = 5 * 8;

struct StateAccounts {
    source: Account,
    storage: Account,
}

fn account_after(result: &mollusk_svm::result::InstructionResult, key: &Pubkey) -> Account {
    result
        .resulting_accounts
        .iter()
        .find(|(actual, _)| actual == key)
        .expect("resulting account")
        .1
        .clone()
}

fn initialized(
    name: &str,
    env_name: &str,
    storage_len: usize,
) -> (Pubkey, Mollusk, Pubkey, Pubkey, StateAccounts) {
    let (program_id, mollusk) = harness(name, env_name);
    let state_key = Pubkey::new_unique();
    let storage_key = Pubkey::new_unique();
    let init = instruction(
        program_id,
        state_key,
        "initialize",
        &[0],
        true,
        true,
        vec![AccountMeta::new_readonly(storage_key, false)],
    );
    let result = mollusk.process_and_validate_instruction(
        &init,
        &[
            (state_key, state_account(&program_id, SOURCE_STATE_LEN)),
            (storage_key, state_account(&program_id, storage_len)),
        ],
        &[Check::success()],
    );
    (
        program_id,
        mollusk,
        state_key,
        storage_key,
        StateAccounts {
            source: account_after(&result, &state_key),
            storage: account_after(&result, &storage_key),
        },
    )
}

fn call(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state_key: Pubkey,
    storage_key: Pubkey,
    accounts: StateAccounts,
    name: &str,
    params: &[u64],
    expected: u64,
) -> StateAccounts {
    let ix = instruction(
        program_id,
        state_key,
        name,
        params,
        true,
        true,
        vec![AccountMeta::new(storage_key, false)],
    );
    let return_data = expected.to_le_bytes();
    let result = mollusk.process_and_validate_instruction(
        &ix,
        &[
            (state_key, accounts.source),
            (storage_key, accounts.storage),
        ],
        &[Check::success(), Check::return_data(&return_data)],
    );
    StateAccounts {
        source: account_after(&result, &state_key),
        storage: account_after(&result, &storage_key),
    }
}

fn call_error(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state_key: Pubkey,
    storage_key: Pubkey,
    accounts: StateAccounts,
    name: &str,
    params: &[u64],
    error: ProgramError,
) -> StateAccounts {
    let ix = instruction(
        program_id,
        state_key,
        name,
        params,
        true,
        true,
        vec![AccountMeta::new(storage_key, false)],
    );
    let before_source = accounts.source.data.clone();
    let before_storage = accounts.storage.data.clone();
    let result = mollusk.process_and_validate_instruction(
        &ix,
        &[
            (state_key, accounts.source),
            (storage_key, accounts.storage),
        ],
        &[
            Check::err(error),
            Check::account(&state_key).data(&before_source).build(),
            Check::account(&storage_key).data(&before_storage).build(),
        ],
    );
    StateAccounts {
        source: account_after(&result, &state_key),
        storage: account_after(&result, &storage_key),
    }
}

#[test]
fn feature_bits_cross_word_boundaries_and_remain_idempotent() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) =
        initialized("FeatureBits", "PF_FEATURE_BITS_SO", FEATURE_STORAGE_LEN);

    for index in [0, 63, 64, 127] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "enable",
            &[index],
            1,
        );
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "enabled",
            &[index],
            1,
        );
    }
    assert_eq!(
        slot(&accounts.storage, 1),
        0x8000_0000_0000_0001,
        "bits 0 and 63 share storage word 2"
    );
    assert_eq!(
        slot(&accounts.storage, 2),
        0x8000_0000_0000_0001,
        "bits 64 and 127 share storage word 3"
    );

    let before_idempotent = accounts.storage.data.clone();
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enable",
        &[64],
        1,
    );
    assert_eq!(
        accounts.storage.data, before_idempotent,
        "idempotent enable must not rewrite membership"
    );

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "disable",
        &[63],
        0,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "toggle",
        &[64],
        0,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "toggle",
        &[64],
        1,
    );
    assert_eq!(slot(&accounts.source, 0), 1, "application State.dummy");
    assert_eq!(slot(&accounts.storage, 1), 1, "disable clears only bit 63");

    accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enable",
        &[128],
        ProgramError::Custom(OUT_OF_RANGE),
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enabled",
        &[u64::MAX],
        0,
    );
    assert_eq!(slot(&accounts.storage, 2), 0x8000_0000_0000_0001);
}

#[test]
fn claims_cover_partial_final_word_and_reject_replay_without_mutation() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) =
        initialized("ClaimBits", "PF_CLAIM_BITS_SO", CLAIM_STORAGE_LEN);

    for index in [0, 63, 64, 128, 129] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "claim",
            &[index],
            1,
        );
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "claimed",
            &[index],
            1,
        );
    }
    assert_eq!(slot(&accounts.storage, 1), 0x8000_0000_0000_0001);
    assert_eq!(slot(&accounts.storage, 2), 1);
    assert_eq!(
        slot(&accounts.storage, 3),
        3,
        "only final-word bits 128/129 are live"
    );
    assert_eq!(
        slot(&accounts.source, 0),
        1,
        "successful claim records its returned membership"
    );

    accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "claim",
        &[64],
        ProgramError::Custom(REPLAY),
    );
    accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "claim",
        &[130],
        ProgramError::Custom(OUT_OF_RANGE),
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "claimed",
        &[130],
        0,
    );
    assert_eq!(
        slot(&accounts.storage, 3),
        3,
        "OOB cannot alias the final word"
    );
}

#[test]
fn selected_word_access_fails_closed_on_short_storage_accounts() {
    let (program_id, mollusk) = harness("FeatureBits", "PF_FEATURE_BITS_SO");
    let state_key = Pubkey::new_unique();
    let storage_key = Pubkey::new_unique();
    let accounts = StateAccounts {
        source: state_account(&program_id, SOURCE_STATE_LEN),
        // Word 3 is required for bit 64, but this account ends immediately before it.
        storage: state_account(&program_id, 3 * 8),
    };
    let _accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enable",
        &[64],
        ProgramError::Custom(1),
    );
}
