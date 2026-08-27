mod common;

use {
    common::{dummy_state_account, dummy_state_key, harness, instruction, plain_account},
    mollusk_svm::{program::create_program_account_loader_v3, result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const TAG: u8 = 7;
const BORSH_TAG: u8 = 8;
const PAIR_TAG: u8 = 9;
const BORSH_PAIR_TAG: u8 = 10;
const ENUM_TAG: u8 = 11;

fn raw_data(small: u8, wide: u64) -> Vec<u8> {
    let mut data = vec![TAG, small];
    data.extend_from_slice(&wide.to_le_bytes());
    data
}

fn bounded_pair_data(left: u64, right: u64) -> Vec<u8> {
    let mut data = vec![PAIR_TAG];
    data.extend_from_slice(&left.to_le_bytes());
    data.extend_from_slice(&right.to_le_bytes());
    data
}

fn borsh_singleton_pair_data(left: u64, right: u64) -> Vec<u8> {
    let mut data = vec![BORSH_PAIR_TAG];
    data.extend_from_slice(&left.to_le_bytes());
    data.extend_from_slice(&right.to_le_bytes());
    data
}

fn enum_wide_data(value: u64) -> Vec<u8> {
    let mut data = vec![ENUM_TAG, 1];
    data.extend_from_slice(&value.to_le_bytes());
    data
}

fn enum_optional_data(present: u8, value: u64) -> Vec<u8> {
    let mut data = vec![ENUM_TAG, 2, present];
    data.extend_from_slice(&value.to_le_bytes());
    data
}

fn borsh_options_data(
    side: u8,
    tick: Option<u64>,
    search: Option<u32>,
    cancel: Option<u32>,
) -> Vec<u8> {
    let mut data = vec![BORSH_TAG, side];
    match tick {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    for value in [search, cancel] {
        match value {
            Some(value) => {
                data.push(1);
                data.extend_from_slice(&value.to_le_bytes());
            }
            None => data.push(0),
        }
    }
    data
}

fn raw_instruction(
    invoked_program: Pubkey,
    protocol_program: Pubkey,
    signer: Pubkey,
    signer_flag: bool,
    data: &[u8],
    trailing: Option<Pubkey>,
) -> Instruction {
    let mut accounts = vec![
        AccountMeta::new_readonly(protocol_program, false),
        AccountMeta::new_readonly(signer, signer_flag),
    ];
    if let Some(key) = trailing {
        accounts.push(AccountMeta::new_readonly(key, false));
    }
    Instruction::new_with_bytes(invoked_program, data, accounts)
}

fn raw_accounts(
    protocol_program: Pubkey,
    program_account: Account,
    signer: Pubkey,
    trailing: Option<Pubkey>,
) -> Vec<(Pubkey, Account)> {
    let mut accounts = vec![
        (protocol_program, program_account),
        (signer, plain_account()),
    ];
    if let Some(key) = trailing {
        accounts.push((key, plain_account()));
    }
    accounts
}

fn expect_raw_error(
    mollusk: &Mollusk,
    invoked_program: Pubkey,
    protocol_program: Pubkey,
    program_account: Account,
    signer_flag: bool,
    data: &[u8],
) {
    let signer = Pubkey::new_unique();
    let ix = raw_instruction(
        invoked_program,
        protocol_program,
        signer,
        signer_flag,
        data,
        None,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(protocol_program, program_account, signer, None),
        &[Check::err(ProgramError::Custom(1))],
    );
}

#[test]
fn packed_u8_and_u64_are_widened_at_exact_offsets() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let ix = raw_instruction(program_id, program_id, signer, true, &raw_data(3, 40), None);
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(
            program_id,
            create_program_account_loader_v3(&program_id),
            signer,
            None,
        ),
        &[Check::success(), Check::return_data(&43u64.to_le_bytes())],
    );
}

#[test]
fn effectful_bounded_pair_returns_two_consecutive_scalars() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    let mut expected = 11u64.to_le_bytes().to_vec();
    expected.extend_from_slice(&29u64.to_le_bytes());
    let ix = raw_instruction(
        program_id,
        program_id,
        signer,
        true,
        &bounded_pair_data(11, 29),
        None,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(program_id, program_account.clone(), signer, None),
        &[Check::success(), Check::return_data(&expected)],
    );
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account,
        true,
        &bounded_pair_data(30, 29),
    );
}

#[test]
fn packed_return_codec_emits_one_borsh_pair() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    let mut expected = 1u32.to_le_bytes().to_vec();
    expected.extend_from_slice(&11u64.to_le_bytes());
    expected.extend_from_slice(&29u64.to_le_bytes());
    let ix = raw_instruction(
        program_id,
        program_id,
        signer,
        true,
        &borsh_singleton_pair_data(11, 29),
        None,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(program_id, program_account.clone(), signer, None),
        &[Check::success(), Check::return_data(&expected)],
    );
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account,
        true,
        &borsh_singleton_pair_data(30, 29),
    );
}

#[test]
fn shared_tag_routes_exact_borsh_enum_variants_and_rejects_other_shapes() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for (data, expected) in [
        (vec![ENUM_TAG, 0, 37], 37u64),
        (
            enum_wide_data(0x1716_1514_1312_1110),
            0x1716_1514_1312_1110u64,
        ),
    ] {
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[
                Check::success(),
                Check::return_data(&expected.to_le_bytes()),
            ],
        );
    }
    for (present, expected) in [(0, None), (1, Some(37u64.to_le_bytes()))] {
        let ix = raw_instruction(
            program_id,
            program_id,
            signer,
            true,
            &enum_optional_data(present, 37),
            None,
        );
        let expected = expected
            .as_ref()
            .map(|bytes| bytes.as_slice())
            .unwrap_or(&[]);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(expected)],
        );
    }
    for malformed in [
        vec![ENUM_TAG, 3, 37],
        vec![ENUM_TAG, 0],
        vec![ENUM_TAG, 0, 37, 0],
        vec![ENUM_TAG, 2],
        enum_optional_data(0, 37)[..10].to_vec(),
        {
            let mut data = enum_optional_data(0, 37);
            data.push(0);
            data
        },
        enum_optional_data(2, 37),
        enum_wide_data(37)[..9].to_vec(),
        {
            let mut data = enum_wide_data(37);
            data.push(0);
            data
        },
        {
            let mut data = enum_wide_data(37);
            data[1] = 0;
            data
        },
    ] {
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &malformed,
        );
    }
}

#[test]
fn variable_borsh_options_decode_all_presence_combinations() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for tick_some in [false, true] {
        for search_some in [false, true] {
            for cancel_some in [false, true] {
                let tick = tick_some.then_some(11);
                let search = search_some.then_some(13);
                let cancel = cancel_some.then_some(17);
                let data = borsh_options_data(3, tick, search, cancel);
                assert!((5..=21).contains(&data.len()));
                let expected = 3
                    + u64::from(tick_some)
                    + tick.unwrap_or_default()
                    + 2 * u64::from(search_some)
                    + u64::from(search.unwrap_or_default())
                    + 4 * u64::from(cancel_some)
                    + u64::from(cancel.unwrap_or_default());
                let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
                mollusk.process_and_validate_instruction(
                    &ix,
                    &raw_accounts(program_id, program_account.clone(), signer, None),
                    &[
                        Check::success(),
                        Check::return_data(&expected.to_le_bytes()),
                    ],
                );
            }
        }
    }
}

#[test]
fn variable_borsh_options_reject_bad_discriminants_truncation_and_trailing_bytes() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let program_account = create_program_account_loader_v3(&program_id);
    for malformed in [
        vec![BORSH_TAG, 0, 2, 0, 0],
        vec![BORSH_TAG, 0, 0, 2, 0],
        vec![BORSH_TAG, 0, 0, 0, 2],
        vec![BORSH_TAG, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        vec![BORSH_TAG, 0, 0, 1, 0, 0, 0],
        vec![BORSH_TAG, 0, 0, 0, 1, 0, 0, 0],
        vec![BORSH_TAG, 0, 0, 0, 0, 0],
    ] {
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &malformed,
        );
    }
}

#[test]
fn declared_prefix_allows_bounded_trailing_accounts() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let trailing = Pubkey::new_unique();
    let ix = raw_instruction(
        program_id,
        program_id,
        signer,
        true,
        &raw_data(255, 1),
        Some(trailing),
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(
            program_id,
            create_program_account_loader_v3(&program_id),
            signer,
            Some(trailing),
        ),
        &[Check::success(), Check::return_data(&256u64.to_le_bytes())],
    );
}

#[test]
fn wrong_tag_and_non_exact_lengths_fail_closed() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let program_account = create_program_account_loader_v3(&program_id);
    let mut wrong_tag = raw_data(3, 40);
    wrong_tag[0] = TAG + 1;
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account.clone(),
        true,
        &wrong_tag,
    );
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account.clone(),
        true,
        &raw_data(3, 40)[..9],
    );
    let mut long = raw_data(3, 40);
    long.push(0);
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account,
        true,
        &long,
    );
}

#[test]
fn missing_signer_fails_closed() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        create_program_account_loader_v3(&program_id),
        false,
        &raw_data(3, 40),
    );
}

#[test]
fn wrong_or_non_executable_program_account_fails_closed() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let wrong_program = Pubkey::new_unique();
    expect_raw_error(
        &mollusk,
        program_id,
        wrong_program,
        create_program_account_loader_v3(&wrong_program),
        true,
        &raw_data(3, 40),
    );
    let non_executable = Pubkey::new_unique();
    expect_raw_error(
        &mollusk,
        program_id,
        non_executable,
        plain_account(),
        true,
        &raw_data(3, 40),
    );
}

#[test]
fn generated_discriminator_path_remains_independent() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let state = dummy_state_key(&program_id);
    let ix = instruction(program_id, state, "get", &[], false, false, vec![]);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state, dummy_state_account(&program_id))],
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}
