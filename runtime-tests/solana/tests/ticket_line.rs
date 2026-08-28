mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const ARITHMETIC_OVERFLOW: u32 = 0x1001;
const SOURCE_STATE_LEN: usize = 2 * 8;
// Full registry region extent: base word 44 + 16 records * 18 words/record.
const STORAGE_LEN: usize = 332 * 8;

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
    let (program_id, mollusk) = harness("TicketLine", "PF_TICKET_LINE_SO");
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
fn fifo_wraps_at_fixed_capacity_and_serves_without_header_overlap() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized();

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineEnqueue",
        &[10],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineEnqueue",
        &[20],
        2,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "linePeek",
        &[],
        10,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineDequeue",
        &[],
        10,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "serve",
        &[],
        20,
    );
    assert_eq!(slot(&accounts.source, 0), 20, "source State.dummy");
    assert_eq!(slot(&accounts.storage, 1), 0, "queue head at word 2");
    assert_eq!(slot(&accounts.storage, 2), 0, "queue count at word 3");

    for ticket in 1..=16 {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "lineEnqueue",
            &[ticket],
            ticket,
        );
    }
    let before_full_push = accounts.storage.data.clone();
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineEnqueue",
        &[99],
        0,
    );
    assert_eq!(
        accounts.storage.data, before_full_push,
        "full enqueue must not mutate"
    );

    for ticket in 1..=15 {
        accounts = call(
            &mollusk,
            program_id,
            state_key,
            storage_key,
            accounts,
            "lineDequeue",
            &[],
            ticket,
        );
    }
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineEnqueue",
        &[17],
        1,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "linePeek",
        &[],
        16,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "lineDequeue",
        &[],
        16,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "linePeek",
        &[],
        17,
    );
    assert_eq!(slot(&accounts.storage, 1), 1, "wrapped head is slot 1");
    assert_eq!(slot(&accounts.storage, 2), 1, "one queued ticket remains");
}

#[test]
fn pod_status_and_ordered_owner_map_compose_on_chain() {
    let (program_id, mollusk, state_key, storage_key, mut accounts) = initialized();

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "setTicketStatus",
        &[1, 7],
        7,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "ticketStatus",
        &[1],
        7,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "registerOwner",
        &[42, 99],
        1,
    );
    assert_eq!(
        slot(&accounts.source, 0),
        1,
        "registered slot in State.dummy"
    );
    assert_eq!(slot(&accounts.storage, 39), 1, "map root at word 40");
    assert_eq!(slot(&accounts.storage, 49), 99, "owner payload at word 50");
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "ownerOf",
        &[42],
        99,
    );

    let duplicate = instruction(
        program_id,
        state_key,
        "registerOwner",
        &[42, 100],
        true,
        true,
        vec![AccountMeta::new(storage_key, false)],
    );
    let before_source = accounts.source.data.clone();
    let before_storage = accounts.storage.data.clone();
    let result = mollusk.process_and_validate_instruction(
        &duplicate,
        &[
            (state_key, accounts.source),
            (storage_key, accounts.storage),
        ],
        &[
            Check::err(ProgramError::Custom(ARITHMETIC_OVERFLOW)),
            Check::account(&state_key).data(&before_source).build(),
            Check::account(&storage_key).data(&before_storage).build(),
        ],
    );
    accounts = StateAccounts {
        source: account_after(&result, &state_key),
        storage: account_after(&result, &storage_key),
    };

    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "releaseOwner",
        &[42],
        0,
    );
    accounts = call(
        &mollusk,
        program_id,
        state_key,
        storage_key,
        accounts,
        "ownerOf",
        &[42],
        0,
    );
    assert_eq!(slot(&accounts.storage, 39), 0, "empty map root");
}
