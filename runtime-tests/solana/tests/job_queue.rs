mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_pubkey::Pubkey,
};

const SOURCE_STATE_LEN: usize = 2 * 8;
const STORAGE_LEN: usize = 21 * 8;

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

fn initialized() -> (Pubkey, Mollusk, Pubkey, Pubkey, StateAccounts) {
    let (program_id, mollusk) = harness("JobQueue", "PF_JOB_QUEUE_SO");
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
            (storage_key, state_account(&program_id, STORAGE_LEN)),
        ],
        &[Check::success()],
    );
    let accounts = StateAccounts {
        source: account_after(&result, &state_key),
        storage: account_after(&result, &storage_key),
    };
    let accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "initializeStorage",
        &[],
        1,
    );
    (program_id, mollusk, state_key, storage_key, accounts)
}

#[test]
fn bounded_vector_composes_without_overlapping_source_state() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized();

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobPush",
        &[11],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobPush",
        &[22],
        2,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobCount",
        &[],
        2,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobGetAt",
        &[1],
        11,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobSetAt",
        &[1, 33],
        33,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobPop",
        &[],
        22,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "publishJob",
        &[44],
        2,
    );

    assert_eq!(slot(&accounts.source, 0), 2, "source State.dummy");
    assert_eq!(slot(&accounts.storage, 3), 2, "vector count at word 4");
    assert_eq!(slot(&accounts.storage, 12), 33, "first job at word 13");
    assert_eq!(slot(&accounts.storage, 13), 44, "second job at word 14");

    for (value, position) in [(55, 3), (66, 4), (77, 5), (88, 6), (99, 7), (111, 8)] {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "jobPush",
            &[value],
            position,
        );
    }
    let before_full_push = accounts.storage.data.clone();
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "jobPush",
        &[222],
        0,
    );
    assert_eq!(
        accounts.storage.data, before_full_push,
        "full push must not mutate"
    );
}

#[test]
fn allocator_reuses_account_resident_free_list_slots() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized();

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotAlloc",
        &[],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotAlloc",
        &[],
        2,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotLiveCount",
        &[],
        2,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotFree",
        &[1],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotFreeListHead",
        &[],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotAlloc",
        &[],
        1,
    );

    assert_eq!(
        slot(&accounts.storage, 1),
        2,
        "allocator live count at word 2"
    );
    assert_eq!(
        slot(&accounts.storage, 2),
        2,
        "bump 2 and empty free list at word 3"
    );
    let before_invalid_free = accounts.storage.data.clone();
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "slotFree",
        &[3],
        0,
    );
    assert_eq!(
        accounts.storage.data, before_invalid_free,
        "never-allocated free must not mutate"
    );
}
