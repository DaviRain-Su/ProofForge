mod common;

use {
    common::{dummy_state_key, harness, instruction},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

fn account_after(result: &mollusk_svm::result::InstructionResult, key: &Pubkey) -> Account {
    result
        .resulting_accounts
        .iter()
        .find(|(actual, _)| actual == key)
        .expect("resulting account")
        .1
        .clone()
}

fn invoke(
    mollusk: &Mollusk,
    program_id: Pubkey,
    state: Account,
    data_key: Pubkey,
    data: Account,
    name: &str,
    params: &[u64],
    writable: bool,
    checks: &[Check],
) -> mollusk_svm::result::InstructionResult {
    let state_key = dummy_state_key(&program_id);
    let meta = if writable {
        AccountMeta::new(data_key, false)
    } else {
        AccountMeta::new_readonly(data_key, false)
    };
    let ix = instruction(
        program_id,
        state_key,
        name,
        params,
        false,
        false,
        vec![meta],
    );
    mollusk.process_and_validate_instruction(&ix, &[(state_key, state), (data_key, data)], checks)
}

fn setup() -> (Pubkey, Mollusk, Pubkey, Account) {
    let (program_id, mollusk) = harness("MemoryOps", "PF_MEMORY_OPS_SO");
    let state_key = dummy_state_key(&program_id);
    let data_key = Pubkey::new_unique();
    let init = instruction(
        program_id,
        state_key,
        "initialize",
        &[0],
        true,
        true,
        vec![AccountMeta::new_readonly(data_key, false)],
    );
    let initialized = mollusk.process_and_validate_instruction(
        &init,
        &[
            (state_key, common::state_account(&program_id, 16)),
            (data_key, Account::new(1_000_000, 24, &program_id)),
        ],
        &[Check::success()],
    );
    (
        program_id,
        mollusk,
        data_key,
        account_after(&initialized, &state_key),
    )
}

#[test]
fn memset_memcpy_and_memcmp_round_trip() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    let zero = 0u64.to_le_bytes();
    let filled = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "fillBytes",
        &[0x111],
        true,
        &[Check::success(), Check::return_data(&zero)],
    );
    let state = account_after(&filled, &dummy_state_key(&program_id));
    let data = account_after(&filled, &data_key);
    assert_eq!(&data.data[..8], &[0x11; 8]);

    let copied = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "copyBytes",
        &[],
        true,
        &[Check::success(), Check::return_data(&zero)],
    );
    let state = account_after(&copied, &dummy_state_key(&program_id));
    let data = account_after(&copied, &data_key);
    assert_eq!(&data.data[..16], &[0x11; 16]);

    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "compareBytes",
        &[],
        false,
        &[Check::success(), Check::return_data(&zero)],
    );
}

#[test]
fn memmove_preserves_overlapping_source_bytes() {
    let (program_id, mollusk, data_key, state) = setup();
    let mut data = Account::new(1_000_000, 24, &program_id);
    for (index, byte) in data.data.iter_mut().enumerate() {
        *byte = index as u8;
    }
    let moved = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "moveBytes",
        &[],
        true,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let data = account_after(&moved, &data_key);
    assert_eq!(&data.data[4..12], &[0, 1, 2, 3, 4, 5, 6, 7]);
}

#[test]
fn memcmp_returns_exact_i32_bits() {
    let (program_id, mollusk, data_key, state) = setup();
    let mut data = Account::new(1_000_000, 24, &program_id);
    data.data[..8].fill(0x11);
    data.data[8..16].fill(0x22);
    let expected = u64::from((-17i32) as u32).to_le_bytes();
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "compareBytes",
        &[],
        false,
        &[Check::success(), Check::return_data(&expected)],
    );
}

#[test]
fn writes_fail_closed_on_permissions_owner_and_length() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "fillBytes",
        &[0xaa],
        false,
        &[Check::err(ProgramError::Custom(1))],
    );

    let wrong_owner = Account::new(1_000_000, 24, &Pubkey::new_unique());
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        wrong_owner,
        "fillBytes",
        &[0xaa],
        true,
        &[Check::err(ProgramError::Custom(1))],
    );

    let short = Account::new(1_000_000, 4, &program_id);
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        short,
        "fillBytes",
        &[0xaa],
        true,
        &[Check::err(ProgramError::Custom(1))],
    );
}
