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
const U128_TAG: u8 = 12;
const BYTES12_TAG: u8 = 13;
const AGGREGATE_TAG: u8 = 14;
const OPTION_SCHEMA_TAG: u8 = 15;
const ENUM_SCHEMA_TAG: u8 = 16;
const BOUNDED_SCHEMA_TAG: u8 = 17;
const BOUNDED_BYTES_TAG: u8 = 18;
const BOUNDED_STRING_TAG: u8 = 19;
const ECHO_BOUNDED_VALUES_TAG: u8 = 20;
const ECHO_BOUNDED_BYTES_TAG: u8 = 21;
const ECHO_BOUNDED_STRING_TAG: u8 = 22;
const MAKE_BOUNDED_STRING_TAG: u8 = 23;
const ECHO_OPTION_TAG: u8 = 24;
const ECHO_TAGGED_TAG: u8 = 25;
const ECHO_PUBKEY_TAG: u8 = 26;
const BYTES_EQUAL_TAG: u8 = 27;
const STRINGS_EQUAL_TAG: u8 = 28;
const BYTES_LESS_TAG: u8 = 29;
const STRINGS_LESS_TAG: u8 = 30;
const BYTES_CONTAINS_TAG: u8 = 31;
const STRINGS_CONTAINS_TAG: u8 = 32;
const BYTES_STARTS_WITH_TAG: u8 = 33;
const STRINGS_STARTS_WITH_TAG: u8 = 34;
const BYTES_ENDS_WITH_TAG: u8 = 35;
const STRINGS_ENDS_WITH_TAG: u8 = 36;

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

fn two_limb_data(tag: u8, w0: u64, w1: u64, final_width: usize) -> Vec<u8> {
    let mut data = vec![tag];
    data.extend_from_slice(&w0.to_le_bytes());
    data.extend_from_slice(&w1.to_le_bytes()[..final_width]);
    data
}

fn aggregate_data(
    amount: u64,
    side: u8,
    enabled: u8,
    pair: (u32, u64),
    levels: [u16; 3],
) -> Vec<u8> {
    let mut data = vec![AGGREGATE_TAG];
    data.extend_from_slice(&amount.to_le_bytes());
    data.push(side);
    data.push(enabled);
    data.extend_from_slice(&pair.0.to_le_bytes());
    data.extend_from_slice(&pair.1.to_le_bytes());
    for level in levels {
        data.extend_from_slice(&level.to_le_bytes());
    }
    data
}

fn pubkey_data(key: &Pubkey) -> Vec<u8> {
    let mut data = vec![ECHO_PUBKEY_TAG];
    data.extend_from_slice(&key.to_bytes());
    data
}

fn bounded_values_data(values: &[u64]) -> Vec<u8> {
    let mut data = vec![BOUNDED_SCHEMA_TAG];
    data.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for value in values {
        data.extend_from_slice(&value.to_le_bytes());
    }
    data
}

fn bounded_bytes_data(tag: u8, bytes: &[u8]) -> Vec<u8> {
    let mut data = vec![tag];
    data.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    data.extend_from_slice(bytes);
    data
}

fn bounded_bytes_pair_data(tag: u8, left: &[u8], right: &[u8]) -> Vec<u8> {
    let mut data = bounded_bytes_data(tag, left);
    data.extend_from_slice(&(right.len() as u32).to_le_bytes());
    data.extend_from_slice(right);
    data
}

fn bounded_u16_data(values: &[u16]) -> Vec<u8> {
    let mut data = vec![ECHO_BOUNDED_VALUES_TAG];
    data.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for value in values {
        data.extend_from_slice(&value.to_le_bytes());
    }
    data
}

fn constructed_string_data(length: u32, bytes: &[u8]) -> Vec<u8> {
    assert!(bytes.len() <= 8);
    let mut data = vec![MAKE_BOUNDED_STRING_TAG];
    data.extend_from_slice(&length.to_le_bytes());
    data.extend_from_slice(bytes);
    data.resize(13, 0);
    data
}

fn tagged_option_data(value: Option<u64>) -> Vec<u8> {
    let mut data = vec![ECHO_OPTION_TAG];
    match value {
        None => data.push(0),
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
    }
    data
}

fn tagged_result_data(variant: u8, payload: &[u64]) -> Vec<u8> {
    let mut data = vec![ECHO_TAGGED_TAG, variant];
    for value in payload {
        data.extend_from_slice(&value.to_le_bytes());
    }
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
fn shared_u128_and_fixed_bytes_use_exact_borsh_limbs() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for data in [
        two_limb_data(U128_TAG, 0x0706_0504_0302_0100, 0x1716_1514_1312_1110, 8),
        two_limb_data(BYTES12_TAG, 0x8786_8584_8382_8180, 0x9796_9594_9392_9190, 4),
    ] {
        let expected = data[1..].to_vec();
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&expected)],
        );

        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &data[..data.len() - 1],
        );
        let mut trailing = data;
        trailing.push(0);
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &trailing,
        );
    }
}

#[test]
fn static_aggregates_use_source_order_borsh_and_canonical_bool() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    let data = aggregate_data(11, 3, 1, (13, 17), [19, 23, 29]);
    assert_eq!(data.len(), 29);
    let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(program_id, program_account.clone(), signer, None),
        &[Check::success(), Check::return_data(&93u64.to_le_bytes())],
    );

    let mut bad_bool = data.clone();
    bad_bool[10] = 2;
    for malformed in [
        bad_bool,
        data[..data.len() - 1].to_vec(),
        {
            let mut trailing = data;
            trailing.push(0);
            trailing
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
fn sdk_pubkey_uses_the_generic_exact_static_record_boundary() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    let key = Pubkey::new_unique();
    let data = pubkey_data(&key);
    assert_eq!(data.len(), 33);
    let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
    mollusk.process_and_validate_instruction(
        &ix,
        &raw_accounts(program_id, program_account.clone(), signer, None),
        &[Check::success(), Check::return_data(&key.to_bytes())],
    );

    for malformed in [data[..data.len() - 1].to_vec(), {
        let mut trailing = data;
        trailing.push(0);
        trailing
    }] {
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
fn logical_option_and_enum_use_canonical_branch_dependent_borsh() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    let mut some = vec![OPTION_SCHEMA_TAG, 1];
    some.extend_from_slice(&37u64.to_le_bytes());
    let mut one = vec![ENUM_SCHEMA_TAG, 1];
    one.extend_from_slice(&7u64.to_le_bytes());
    let mut pair = vec![ENUM_SCHEMA_TAG, 2];
    pair.extend_from_slice(&11u64.to_le_bytes());
    pair.extend_from_slice(&29u64.to_le_bytes());
    for (data, expected) in [
        (vec![OPTION_SCHEMA_TAG, 0], 5u64),
        (some, 38u64),
        (vec![ENUM_SCHEMA_TAG, 0], 3u64),
        (one, 17u64),
        (pair, 40u64),
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

    let mut short_some = vec![OPTION_SCHEMA_TAG, 1];
    short_some.extend_from_slice(&37u32.to_le_bytes());
    let mut short_pair = vec![ENUM_SCHEMA_TAG, 2];
    short_pair.extend_from_slice(&11u64.to_le_bytes());
    for malformed in [
        vec![OPTION_SCHEMA_TAG, 2],
        short_some,
        vec![OPTION_SCHEMA_TAG, 0, 0],
        vec![ENUM_SCHEMA_TAG, 3],
        short_pair,
        vec![ENUM_SCHEMA_TAG, 0, 0],
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
fn bounded_vec_uses_canonical_u32_length_and_fixed_zeroed_locals() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for (values, expected) in [
        (vec![], 0u64),
        (vec![11, 13], 13u64),
        (vec![17, 19, 23, 29], 50u64),
    ] {
        let data = bounded_values_data(&values);
        assert!((5..=37).contains(&data.len()));
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

    let mut too_many = vec![BOUNDED_SCHEMA_TAG];
    too_many.extend_from_slice(&5u32.to_le_bytes());
    for value in [1u64, 2, 3, 4, 5] {
        too_many.extend_from_slice(&value.to_le_bytes());
    }
    let mut short = vec![BOUNDED_SCHEMA_TAG];
    short.extend_from_slice(&2u32.to_le_bytes());
    short.extend_from_slice(&11u64.to_le_bytes());
    let mut trailing = bounded_values_data(&[7]);
    trailing.extend_from_slice(&9u64.to_le_bytes());
    for malformed in [
        vec![BOUNDED_SCHEMA_TAG, 0, 0, 0],
        too_many,
        short,
        trailing,
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
fn bounded_bytes_use_canonical_borsh_vec_u8_and_fixed_zeroed_locals() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for (bytes, expected) in [
        (vec![], 0u64),
        (vec![11, 13], 13u64),
        (vec![17, 19, 23, 29, 31, 37, 41, 43], 68u64),
    ] {
        let data = bounded_bytes_data(BOUNDED_BYTES_TAG, &bytes);
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

    let mut over_capacity = bounded_bytes_data(BOUNDED_BYTES_TAG, &[1; 9]);
    let mut truncated = bounded_bytes_data(BOUNDED_BYTES_TAG, &[11, 13]);
    truncated.pop();
    let mut trailing = bounded_bytes_data(BOUNDED_BYTES_TAG, &[11]);
    trailing.push(13);
    for malformed in [&mut over_capacity, &mut truncated, &mut trailing] {
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            malformed,
        );
    }
}

#[test]
fn bounded_string_enforces_strict_utf8_before_source_observation() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for text in [
        vec![],
        b"abc".to_vec(),
        vec![0xc2, 0xa2],
        vec![0xe2, 0x82, 0xac],
        vec![0xf0, 0x9f, 0x92, 0xa9],
        b"abcdefgh".to_vec(),
    ] {
        let expected = text.len() as u64
            + u64::from(text.first().copied().unwrap_or_default())
            + u64::from(text.get(7).copied().unwrap_or_default());
        let data = bounded_bytes_data(BOUNDED_STRING_TAG, &text);
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

    for malformed in [
        vec![0x80],
        vec![0xc0, 0x80],
        vec![0xe0, 0x80, 0x80],
        vec![0xed, 0xa0, 0x80],
        vec![0xe2, 0x82],
        vec![0xf4, 0x90, 0x80, 0x80],
        vec![0xf5, 0x80, 0x80, 0x80],
    ] {
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &bounded_bytes_data(BOUNDED_STRING_TAG, &malformed),
        );
    }
}

#[test]
fn bounded_bytes_and_strings_compare_and_search_canonical_active_prefixes() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);
    for (tag, left, right, expected) in [
        (BYTES_EQUAL_TAG, vec![], vec![], 1u8),
        (BYTES_EQUAL_TAG, b"abc".to_vec(), b"abc".to_vec(), 1),
        (BYTES_EQUAL_TAG, b"abc".to_vec(), b"abd".to_vec(), 0),
        (BYTES_EQUAL_TAG, b"abc".to_vec(), b"ab".to_vec(), 0),
        (
            STRINGS_EQUAL_TAG,
            vec![0xe2, 0x82, 0xac],
            vec![0xe2, 0x82, 0xac],
            1,
        ),
        (
            STRINGS_EQUAL_TAG,
            vec![0xc2, 0xa2],
            vec![0xe2, 0x82, 0xac],
            0,
        ),
        (BYTES_LESS_TAG, vec![], vec![], 0),
        (BYTES_LESS_TAG, b"abc".to_vec(), b"abd".to_vec(), 1),
        (BYTES_LESS_TAG, b"abd".to_vec(), b"abc".to_vec(), 0),
        (BYTES_LESS_TAG, b"ab".to_vec(), b"abc".to_vec(), 1),
        (BYTES_LESS_TAG, b"abc".to_vec(), b"ab".to_vec(), 0),
        (
            STRINGS_LESS_TAG,
            vec![0xc2, 0xa2],
            vec![0xe2, 0x82, 0xac],
            1,
        ),
        (
            STRINGS_LESS_TAG,
            vec![0xe2, 0x82, 0xac],
            vec![0xc2, 0xa2],
            0,
        ),
        (BYTES_CONTAINS_TAG, vec![], vec![], 1),
        (BYTES_CONTAINS_TAG, vec![], b"a".to_vec(), 0),
        (BYTES_CONTAINS_TAG, b"abc".to_vec(), vec![], 1),
        (BYTES_CONTAINS_TAG, b"ababa".to_vec(), b"aba".to_vec(), 1),
        (BYTES_CONTAINS_TAG, b"abc".to_vec(), b"bc".to_vec(), 1),
        (BYTES_CONTAINS_TAG, b"abc".to_vec(), b"ac".to_vec(), 0),
        (BYTES_CONTAINS_TAG, b"abc".to_vec(), b"abcd".to_vec(), 0),
        (
            STRINGS_CONTAINS_TAG,
            vec![0xc2, 0xa2, 0xe2, 0x82, 0xac],
            vec![0xe2, 0x82, 0xac],
            1,
        ),
        (
            STRINGS_CONTAINS_TAG,
            vec![0xe2, 0x82, 0xac],
            vec![0xc2, 0xa2],
            0,
        ),
        (BYTES_STARTS_WITH_TAG, vec![], vec![], 1),
        (BYTES_STARTS_WITH_TAG, vec![], b"a".to_vec(), 0),
        (BYTES_STARTS_WITH_TAG, b"abc".to_vec(), vec![], 1),
        (BYTES_STARTS_WITH_TAG, b"abc".to_vec(), b"ab".to_vec(), 1),
        (BYTES_STARTS_WITH_TAG, b"abc".to_vec(), b"abc".to_vec(), 1),
        (BYTES_STARTS_WITH_TAG, b"abc".to_vec(), b"bc".to_vec(), 0),
        (BYTES_STARTS_WITH_TAG, b"abc".to_vec(), b"abcd".to_vec(), 0),
        (BYTES_ENDS_WITH_TAG, vec![], vec![], 1),
        (BYTES_ENDS_WITH_TAG, vec![], b"a".to_vec(), 0),
        (BYTES_ENDS_WITH_TAG, b"abc".to_vec(), vec![], 1),
        (BYTES_ENDS_WITH_TAG, b"abc".to_vec(), b"bc".to_vec(), 1),
        (BYTES_ENDS_WITH_TAG, b"abc".to_vec(), b"abc".to_vec(), 1),
        (BYTES_ENDS_WITH_TAG, b"abc".to_vec(), b"ab".to_vec(), 0),
        (BYTES_ENDS_WITH_TAG, b"abc".to_vec(), b"abcd".to_vec(), 0),
        (
            STRINGS_STARTS_WITH_TAG,
            vec![0xe2, 0x82, 0xac, 0xc2, 0xa2],
            vec![0xe2, 0x82, 0xac],
            1,
        ),
        (
            STRINGS_STARTS_WITH_TAG,
            vec![0xe2, 0x82, 0xac, 0xc2, 0xa2],
            vec![0xc2, 0xa2],
            0,
        ),
        (
            STRINGS_ENDS_WITH_TAG,
            vec![0xe2, 0x82, 0xac, 0xc2, 0xa2],
            vec![0xc2, 0xa2],
            1,
        ),
        (
            STRINGS_ENDS_WITH_TAG,
            vec![0xe2, 0x82, 0xac, 0xc2, 0xa2],
            vec![0xe2, 0x82, 0xac],
            0,
        ),
    ] {
        let data = bounded_bytes_pair_data(tag, &left, &right);
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&[expected])],
        );
    }

    for tag in [
        STRINGS_EQUAL_TAG,
        STRINGS_LESS_TAG,
        STRINGS_CONTAINS_TAG,
        STRINGS_STARTS_WITH_TAG,
        STRINGS_ENDS_WITH_TAG,
    ] {
        for (left, right) in [
            (vec![0xc0, 0x80], b"abc".to_vec()),
            (b"abc".to_vec(), vec![0xed, 0xa0, 0x80]),
        ] {
            expect_raw_error(
                &mollusk,
                program_id,
                program_id,
                program_account.clone(),
                true,
                &bounded_bytes_pair_data(tag, &left, &right),
            );
        }
    }
}

#[test]
fn bounded_returns_publish_only_the_canonical_borsh_active_prefix() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);

    for values in [vec![], vec![11u16, 13], vec![17, 19, 23, 29]] {
        let data = bounded_u16_data(&values);
        let expected = data[1..].to_vec();
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&expected)],
        );
    }

    for (tag, values) in [
        (ECHO_BOUNDED_BYTES_TAG, vec![]),
        (ECHO_BOUNDED_BYTES_TAG, vec![0x80, 0xff]),
        (ECHO_BOUNDED_BYTES_TAG, b"abcdefgh".to_vec()),
        (ECHO_BOUNDED_STRING_TAG, vec![]),
        (ECHO_BOUNDED_STRING_TAG, vec![0xe2, 0x82, 0xac]),
        (ECHO_BOUNDED_STRING_TAG, b"abcdefgh".to_vec()),
    ] {
        let data = bounded_bytes_data(tag, &values);
        let expected = data[1..].to_vec();
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&expected)],
        );
    }
}

#[test]
fn tagged_returns_publish_canonical_branch_dependent_borsh() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);

    let cases = [
        tagged_option_data(None),
        tagged_option_data(Some(37)),
        tagged_result_data(0, &[]),
        tagged_result_data(1, &[41]),
        tagged_result_data(2, &[43, 47]),
    ];
    for data in cases {
        let expected = data[1..].to_vec();
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&expected)],
        );
    }
}

#[test]
fn constructed_string_validates_utf8_at_the_output_boundary() {
    let (program_id, mollusk) = harness("RawEntry", "PF_RAW_ENTRY_SO");
    let signer = Pubkey::new_unique();
    let program_account = create_program_account_loader_v3(&program_id);

    for text in [
        vec![],
        b"abc".to_vec(),
        vec![0xc2, 0xa2],
        vec![0xe2, 0x82, 0xac],
        vec![0xf0, 0x9f, 0x92, 0xa9],
        b"abcdefgh".to_vec(),
    ] {
        let data = constructed_string_data(text.len() as u32, &text);
        let mut expected = (text.len() as u32).to_le_bytes().to_vec();
        expected.extend_from_slice(&text);
        let ix = raw_instruction(program_id, program_id, signer, true, &data, None);
        mollusk.process_and_validate_instruction(
            &ix,
            &raw_accounts(program_id, program_account.clone(), signer, None),
            &[Check::success(), Check::return_data(&expected)],
        );
    }

    for malformed in [
        vec![0x80],
        vec![0xc0, 0x80],
        vec![0xe0, 0x80, 0x80],
        vec![0xed, 0xa0, 0x80],
        vec![0xe2, 0x82],
        vec![0xf4, 0x90, 0x80, 0x80],
        vec![0xf5, 0x80, 0x80, 0x80],
    ] {
        expect_raw_error(
            &mollusk,
            program_id,
            program_id,
            program_account.clone(),
            true,
            &constructed_string_data(malformed.len() as u32, &malformed),
        );
    }
    expect_raw_error(
        &mollusk,
        program_id,
        program_id,
        program_account,
        true,
        &constructed_string_data(9, b"abcdefgh"),
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
