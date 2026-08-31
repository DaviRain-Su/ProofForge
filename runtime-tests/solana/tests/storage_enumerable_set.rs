mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

// Most arbitrary named source errors currently share the SVM generic fail-closed code;
// the SDK's canonical full condition has its own stable code.
const SET_ERROR: u32 = 1;
const FULL: u32 = 0x1003;
const SOURCE_STATE_LEN: usize = 2 * 8;
// MemberDirectory's final position payload is word 37 (capacity 4, seven-word nodes).
const DIRECTORY_STORAGE_LEN: usize = 38 * 8;
// UniqueRoster's final position payload is word 46 (capacity 5, seven-word nodes).
const ROSTER_STORAGE_LEN: usize = 47 * 8;

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

fn set_slot(account: &mut Account, index: usize, value: u64) {
    let offset = 8 + index * 8;
    account.data[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn source_initialized(
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
    let result = mollusk.process_and_validate_instruction(
        &ix,
        &[
            (state_key, accounts.source),
            (storage_key, accounts.storage),
        ],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
        ],
    );
    StateAccounts {
        source: account_after(&result, &state_key),
        storage: account_after(&result, &storage_key),
    }
}

fn call_error_code(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state_key: Pubkey,
    storage_key: Pubkey,
    accounts: StateAccounts,
    name: &str,
    params: &[u64],
    error: u32,
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
            Check::err(ProgramError::Custom(error)),
            Check::account(&state_key).data(&before_source).build(),
            Check::account(&storage_key).data(&before_storage).build(),
        ],
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
) -> StateAccounts {
    call_error_code(
        mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        name,
        params,
        SET_ERROR,
    )
}

fn initialize_storage(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state_key: Pubkey,
    storage_key: Pubkey,
    accounts: StateAccounts,
) -> StateAccounts {
    call(
        mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "initializeStorage",
        &[],
        1,
    )
}

fn initialized(
    name: &str,
    env_name: &str,
    storage_len: usize,
) -> (Pubkey, Mollusk, Pubkey, Pubkey, StateAccounts) {
    let (program_id, mollusk, state_key, storage_key, accounts) =
        source_initialized(name, env_name, storage_len);
    let accounts = initialize_storage(&mollusk, program_id, state_key, storage_key, accounts);
    (program_id, mollusk, state_key, storage_key, accounts)
}

#[test]
fn directory_requires_initialization_and_enumerates_zero_as_a_member() {
    let (program_id, mollusk, state_key, storage_key, accounts) = source_initialized(
        "MemberDirectory",
        "PF_MEMBER_DIRECTORY_SO",
        DIRECTORY_STORAGE_LEN,
    );
    let accounts = call_error_code(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "add",
        &[7],
        0x1001,
    );
    assert!(accounts.storage.data.iter().all(|byte| *byte == 0));

    let mut accounts = initialize_storage(&mollusk, program_id, state_key, storage_key, accounts);
    for member in [0, 11, 22] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "add",
            &[member],
            1,
        );
    }
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "contains",
        &[0],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "size",
        &[],
        3,
    );
    for (index, member) in [(0, 0), (1, 11), (2, 22), (3, 0)] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "valueAt",
            &[index],
            member,
        );
    }
    assert_eq!(slot(&accounts.storage, 1), 0, "value zero at word 2");
    assert_eq!(slot(&accounts.storage, 2), 11, "second active value");
    assert_eq!(slot(&accounts.storage, 3), 22, "third active value");
    assert_eq!(slot(&accounts.storage, 7), 3, "canonical map/live count");
}

#[test]
fn directory_swap_remove_repairs_positions_then_removes_last_and_only() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized(
        "MemberDirectory",
        "PF_MEMBER_DIRECTORY_SO",
        DIRECTORY_STORAGE_LEN,
    );
    for member in [0, 11, 22] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "add",
            &[member],
            1,
        );
    }

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "remove",
        &[11],
        1,
    );
    assert_eq!(
        slot(&accounts.storage, 2),
        22,
        "last value moved into position 2"
    );
    assert_eq!(
        slot(&accounts.storage, 29),
        2,
        "node 3 reverse position repaired at word 30"
    );
    assert_eq!(slot(&accounts.storage, 7), 2, "count after middle removal");
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "contains",
        &[22],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "remove",
        &[22],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "remove",
        &[0],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "size",
        &[],
        0,
    );
    accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "remove",
        &[0],
    );
    assert_eq!(slot(&accounts.storage, 5), 0, "empty tree root");
}

#[test]
fn strict_directory_duplicate_and_full_errors_roll_back_atomically() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized(
        "MemberDirectory",
        "PF_MEMBER_DIRECTORY_SO",
        DIRECTORY_STORAGE_LEN,
    );
    for member in [1, 2, 3, 4] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "add",
            &[member],
            1,
        );
    }
    accounts = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "add",
        &[3],
    );
    accounts = call_error_code(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "add",
        &[5],
        FULL,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "size",
        &[],
        4,
    );
    assert_eq!(slot(&accounts.storage, 7), 4);
}

#[test]
fn malformed_metadata_and_short_storage_fail_before_partial_set_mutation() {
    let (program_id, mollusk, state_key, storage_key, mut canonical) = initialized(
        "MemberDirectory",
        "PF_MEMBER_DIRECTORY_SO",
        DIRECTORY_STORAGE_LEN,
    );
    for member in [10, 20, 30] {
        canonical = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            canonical,
            "add",
            &[member],
            1,
        );
    }

    let mut forged_position = StateAccounts {
        source: canonical.source.clone(),
        storage: canonical.storage.clone(),
    };
    // Node 2 position payload is word 23; count is 3, so position 4 is forged.
    set_slot(&mut forged_position.storage, 22, 4);
    let forged_position = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        forged_position,
        "remove",
        &[20],
    );
    assert_eq!(slot(&forged_position.storage, 22), 4);

    let mut forged_backing = StateAccounts {
        source: canonical.source.clone(),
        storage: canonical.storage.clone(),
    };
    // Position 2 points at word 3; it must agree with key 20 before any map removal.
    set_slot(&mut forged_backing.storage, 2, 999);
    let forged_backing = call_error(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        forged_backing,
        "remove",
        &[20],
    );
    assert_eq!(slot(&forged_backing.storage, 2), 999);

    let mut forged_count = StateAccounts {
        source: canonical.source.clone(),
        storage: canonical.storage.clone(),
    };
    // Map live count is word 8; a count above capacity must not make a valid node observable.
    set_slot(&mut forged_count.storage, 7, 5);
    let forged_count = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        forged_count,
        "contains",
        &[20],
        0,
    );
    let forged_count = call_error_code(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        forged_count,
        "add",
        &[20],
        FULL,
    );
    assert_eq!(slot(&forged_count.storage, 7), 5);

    let (short_program_id, short_mollusk, short_state_key, short_storage_key, short_accounts) =
        initialized(
            "MemberDirectory",
            "PF_MEMBER_DIRECTORY_SO",
            DIRECTORY_STORAGE_LEN - 8,
        );
    let short_accounts = call_error(
        &short_mollusk,
        short_program_id,
        short_state_key,
        short_storage_key,
        short_accounts,
        "add",
        &[1],
    );
    assert_eq!(
        slot(&short_accounts.storage, 7),
        0,
        "short-account insert left the initialized count unchanged"
    );
}

#[test]
fn roster_policy_is_idempotent_but_still_bounded() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) =
        initialized("UniqueRoster", "PF_UNIQUE_ROSTER_SO", ROSTER_STORAGE_LEN);
    for identity in [0, 7, 8, 9, 10] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "enroll",
            &[identity],
            1,
        );
    }
    let before_duplicate = accounts.storage.data.clone();
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enroll",
        &[7],
        1,
    );
    assert_eq!(accounts.storage.data, before_duplicate);
    accounts = call_error_code(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enroll",
        &[11],
        FULL,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "withdraw",
        &[42],
        0,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "withdraw",
        &[8],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "enrolled",
        &[8],
        0,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "size",
        &[],
        4,
    );
    assert_eq!(slot(&accounts.storage, 9), 4, "roster count at word 10");
}
