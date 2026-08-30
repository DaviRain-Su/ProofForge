mod common;

use {
    common::{dummy_state_key, harness, instruction},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_svm_log_collector::LogCollector,
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

fn resizable_account(program_id: &Pubkey, data: Vec<u8>) -> Account {
    let mut account = Account::new(10_000_000_000, data.len(), program_id);
    account.data = data;
    account
}

#[test]
fn account_resize_grows_with_zeroes_and_shrinks_to_the_prefix() {
    let (program_id, mollusk, data_key, state) = setup();
    let original = (1u8..=8).collect::<Vec<_>>();
    let grown = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        resizable_account(&program_id, original.clone()),
        "resizeData",
        &[16],
        true,
        &[Check::success(), Check::return_data(&16u64.to_le_bytes())],
    );
    let state = account_after(&grown, &dummy_state_key(&program_id));
    let data = account_after(&grown, &data_key);
    assert_eq!(data.data.len(), 16);
    assert_eq!(&data.data[..8], original);
    assert_eq!(&data.data[8..], &[0; 8]);

    let shrunk = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "resizeData",
        &[6],
        true,
        &[Check::success(), Check::return_data(&6u64.to_le_bytes())],
    );
    let data = account_after(&shrunk, &data_key);
    assert_eq!(data.data, original[..6]);
}

#[test]
fn account_resize_shrink_then_grow_zeroes_reexposed_bytes() {
    let (program_id, mollusk, data_key, state) = setup();
    let original = (1u8..=8).collect::<Vec<_>>();
    let resized = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        resizable_account(&program_id, original.clone()),
        "shrinkThenGrow",
        &[4, 12],
        true,
        &[Check::success(), Check::return_data(&12u64.to_le_bytes())],
    );
    let data = account_after(&resized, &data_key);
    assert_eq!(data.data.len(), 12);
    assert_eq!(&data.data[..4], &original[..4]);
    assert_eq!(&data.data[4..], &[0; 8]);
}

#[test]
fn account_resize_is_visible_to_following_checked_memory_effects() {
    let (program_id, mollusk, data_key, state) = setup();
    let original = (1u8..=8).collect::<Vec<_>>();
    let resized = invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        resizable_account(&program_id, original.clone()),
        "resizeThenFill",
        &[16, 0xab],
        true,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let data = account_after(&resized, &data_key);
    assert_eq!(&data.data[..8], original);
    assert_eq!(&data.data[8..], &[0xab; 8]);
}

#[test]
fn account_resize_enforces_original_growth_budget_and_account_ceiling_atomically() {
    let (program_id, mollusk, data_key, state) = setup();
    let original = vec![0x5a; 8];
    let boundary = invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        resizable_account(&program_id, original.clone()),
        "resizeData",
        &[8 + 10_240],
        true,
        &[
            Check::success(),
            Check::return_data(&(8u64 + 10_240).to_le_bytes()),
        ],
    );
    let boundary_data = account_after(&boundary, &data_key);
    assert_eq!(boundary_data.data.len(), 8 + 10_240);
    assert_eq!(&boundary_data.data[..8], original);
    assert!(boundary_data.data[8..].iter().all(|byte| *byte == 0));

    for requested in [8u64 + 10_241, 10 * 1024 * 1024 + 1] {
        let failed = invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            resizable_account(&program_id, original.clone()),
            "resizeData",
            &[requested],
            true,
            &[Check::err(ProgramError::Custom(1))],
        );
        assert_eq!(account_after(&failed, &data_key).data, original);
    }
}

#[test]
fn account_resize_rejects_readonly_foreign_owned_and_managed_state_aliases() {
    let (program_id, mollusk, data_key, state) = setup();
    let original = vec![0x5a; 8];
    let readonly = invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        resizable_account(&program_id, original.clone()),
        "resizeData",
        &[16],
        false,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(account_after(&readonly, &data_key).data, original);

    let foreign_owner = Pubkey::new_unique();
    let foreign = invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        resizable_account(&foreign_owner, original.clone()),
        "resizeData",
        &[16],
        true,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(account_after(&foreign, &data_key).data, original);

    let state_key = dummy_state_key(&program_id);
    let alias_ix = instruction(
        program_id,
        state_key,
        "resizeData",
        &[24],
        false,
        false,
        vec![AccountMeta::new(state_key, false)],
    );
    let alias = mollusk.process_and_validate_instruction(
        &alias_ix,
        &[(state_key, state.clone())],
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(account_after(&alias, &state_key).data, state.data);
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

#[test]
fn transient_vector_push_set_get_clear_and_length() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "vectorSetGet",
        &[11, 22, 33, 0],
        false,
        &[Check::success(), Check::return_data(&11u64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "vectorSetGet",
        &[11, 22, 33, 1],
        false,
        &[Check::success(), Check::return_data(&33u64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "vectorLengthAfterClear",
        &[55],
        false,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn transient_vector_truncate_only_shortens_the_live_prefix() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    for (new_length, expected) in [(1u64, 1u64), (2, 2), (u64::MAX, 2)] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            data.clone(),
            "vectorLengthAfterTruncate",
            &[new_length],
            false,
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn transient_vector_pop_is_lifo_and_rejects_empty() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "vectorPop",
        &[11, 22],
        false,
        &[Check::success(), Check::return_data(&22u64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "vectorPopEmpty",
        &[],
        false,
        &[Check::err(ProgramError::Custom(0x1202))],
    );
}

#[test]
fn transient_vector_reports_bounds_stale_handle_and_oom() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    for (name, error) in [
        ("vectorOverflow", 0x1202),
        ("vectorOutOfBounds", 0x1202),
        ("vectorWrongCapacity", 0x1203),
        ("vectorAfterFinish", 0x1203),
        ("vectorOom", 0x1201),
    ] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            data.clone(),
            name,
            &[],
            false,
            &[Check::err(ProgramError::Custom(error))],
        );
    }
}

#[test]
fn transient_bytes_push_set_get_clear_and_length() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "bytesSetGet",
        &[0x11, 0x22, 0xff, 0],
        false,
        &[Check::success(), Check::return_data(&0x11u64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "bytesSetGet",
        &[0x11, 0x22, 0xff, 1],
        false,
        &[Check::success(), Check::return_data(&0xffu64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "bytesLengthAfterClear",
        &[0x33],
        false,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn transient_bytes_truncate_only_shortens_the_live_prefix() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    for (new_length, expected) in [(1u64, 1u64), (2, 2), (u64::MAX, 2)] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            data.clone(),
            "bytesLengthAfterTruncate",
            &[new_length],
            false,
            &[Check::success(), Check::return_data(&expected.to_le_bytes())],
        );
    }
}

#[test]
fn transient_bytes_pop_is_lifo_and_rejects_empty() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "bytesPop",
        &[0x11, 0xff],
        false,
        &[Check::success(), Check::return_data(&0xffu64.to_le_bytes())],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "bytesPopEmpty",
        &[],
        false,
        &[Check::err(ProgramError::Custom(0x1212))],
    );
}

#[test]
fn transient_bytes_append_le64_keeps_little_endian_byte_order() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    let value = 0x1122334455667788u64;
    let expected_low = (value & 0xff).to_le_bytes();
    let expected_high = (value >> 56).to_le_bytes();
    invoke(
        &mollusk,
        program_id,
        state.clone(),
        data_key,
        data.clone(),
        "bytesAppendLe64",
        &[value, 0],
        false,
        &[Check::success(), Check::return_data(&expected_low)],
    );
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "bytesAppendLe64",
        &[value, 7],
        false,
        &[Check::success(), Check::return_data(&expected_high)],
    );
}

#[test]
fn transient_bytes_log_data_publishes_live_payload_and_preserves_return_data() {
    let (program_id, mut mollusk, data_key, state) = setup();
    mollusk.logger = Some(LogCollector::new_ref_with_limit(None));
    let data = Account::new(1_000_000, 24, &program_id);
    invoke(
        &mollusk,
        program_id,
        state,
        data_key,
        data,
        "bytesLogData",
        &[0x1122334455667788, 0xaa],
        false,
        &[Check::success(), Check::return_data(&9u64.to_le_bytes())],
    );
    let logger = mollusk.logger.as_ref().expect("memory ops logger").borrow();
    let messages = logger.get_recorded_content();
    assert!(
        messages
            .iter()
            .any(|message| message == "Program data: iHdmVUQzIhGq"),
        "missing exact bounded log-data payload: {messages:?}"
    );
}

#[test]
fn transient_bytes_coexist_with_transient_vector() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    for (word, byte) in [(0x0102030405060708u64, 0xaau64), (0xff11ee22dd33cc44, 0x42)] {
        let expected = (byte + word).to_le_bytes();
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            data.clone(),
            "vectorWithBytes",
            &[word, byte],
            false,
            &[Check::success(), Check::return_data(&expected)],
        );
    }
}

#[test]
fn transient_bytes_reports_bounds_range_stale_handle_and_oom() {
    let (program_id, mollusk, data_key, state) = setup();
    let data = Account::new(1_000_000, 24, &program_id);
    for (name, error) in [
        ("bytesOverflow", 0x1212),
        ("bytesOutOfBounds", 0x1212),
        ("bytesWrongCapacity", 0x1213),
        ("bytesAfterFinish", 0x1213),
        ("bytesPushOverRange", 0x1214),
        ("bytesSetOverRange", 0x1214),
        ("bytesOom", 0x1211),
    ] {
        invoke(
            &mollusk,
            program_id,
            state.clone(),
            data_key,
            data.clone(),
            name,
            &[],
            false,
            &[Check::err(ProgramError::Custom(error))],
        );
    }
}
