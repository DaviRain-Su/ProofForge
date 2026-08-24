mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_pubkey::Pubkey,
};

const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const STATE_LEN: usize = 16;
const LOG_TAG: u8 = 15;

fn initialized_state(program_id: &Pubkey) -> Account {
    let mut state = common::state_account(program_id, STATE_LEN);
    let layout = "1|0:count:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout}").as_bytes());
    let marker = u64::from_be_bytes(digest[..8].try_into().expect("layout marker"));
    state.data[..8].copy_from_slice(&marker.to_le_bytes());
    state
}

fn harness() -> (Pubkey, Pubkey, Mollusk) {
    let (program_id, mollusk) = common::harness("SelfLog", "PF_SELF_LOG_SO");
    let (authority, _) = Pubkey::find_program_address(&[b"log"], &program_id);
    (program_id, authority, mollusk)
}

fn self_program_account(program_id: &Pubkey) -> Account {
    mollusk_svm::program::create_program_account_loader_v3(program_id)
}

fn outer_instruction(
    program_id: Pubkey,
    state_key: Pubkey,
    authority: Pubkey,
    authority_signer: bool,
    authority_writable: bool,
    value: u64,
) -> Instruction {
    let authority_meta = match (authority_writable, authority_signer) {
        (true, signer) => AccountMeta::new(authority, signer),
        (false, signer) => AccountMeta::new_readonly(authority, signer),
    };
    common::instruction(
        program_id,
        state_key,
        "record",
        &[value],
        true,
        false,
        vec![authority_meta, AccountMeta::new_readonly(program_id, false)],
    )
}

fn outer_accounts(
    program_id: Pubkey,
    state_key: Pubkey,
    authority: Pubkey,
) -> Vec<(Pubkey, Account)> {
    vec![
        (state_key, initialized_state(&program_id)),
        (authority, common::plain_account()),
        (program_id, self_program_account(&program_id)),
    ]
}

fn assert_rejected(result: &mollusk_svm::result::InstructionResult) {
    assert!(
        result.raw_result.is_err(),
        "malformed raw self-entry unexpectedly succeeded: {:?}",
        result.program_result
    );
}

#[test]
fn signed_self_cpi_records_and_continues_state_writeback() {
    let (program_id, authority, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let value = 42;
    let ix = outer_instruction(program_id, state_key, authority, false, false, value);
    mollusk.process_and_validate_instruction(
        &ix,
        &outer_accounts(program_id, state_key, authority),
        &[
            Check::success(),
            Check::return_data(&value.to_le_bytes()),
            Check::account(&state_key)
                .data_slice(8, &value.to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn signed_self_cpi_rejects_wrong_authority() {
    let (program_id, _authority, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let wrong = Pubkey::new_unique();
    let ix = outer_instruction(program_id, state_key, wrong, false, false, 42);
    let result = mollusk.process_instruction(&ix, &outer_accounts(program_id, state_key, wrong));
    assert_rejected(&result);
}

#[test]
fn direct_raw_entry_accepts_only_the_canonical_readonly_signer_and_tag() {
    let (program_id, authority, mollusk) = harness();
    let authority_account = common::plain_account();
    let valid = Instruction::new_with_bytes(
        program_id,
        &[LOG_TAG, 1, 2, 3],
        vec![AccountMeta::new_readonly(authority, true)],
    );
    mollusk.process_and_validate_instruction(
        &valid,
        &[(authority, authority_account.clone())],
        &[Check::success()],
    );

    let missing_signer = Instruction::new_with_bytes(
        program_id,
        &[LOG_TAG],
        vec![AccountMeta::new_readonly(authority, false)],
    );
    assert_rejected(
        &mollusk.process_instruction(&missing_signer, &[(authority, authority_account.clone())]),
    );

    let writable = Instruction::new_with_bytes(
        program_id,
        &[LOG_TAG],
        vec![AccountMeta::new(authority, true)],
    );
    assert_rejected(
        &mollusk.process_instruction(&writable, &[(authority, authority_account.clone())]),
    );

    let wrong_tag = Instruction::new_with_bytes(
        program_id,
        &[LOG_TAG - 1],
        vec![AccountMeta::new_readonly(authority, true)],
    );
    assert_rejected(
        &mollusk.process_instruction(&wrong_tag, &[(authority, authority_account.clone())]),
    );

    let wrong_authority = Pubkey::new_unique();
    let wrong_key = Instruction::new_with_bytes(
        program_id,
        &[LOG_TAG],
        vec![AccountMeta::new_readonly(wrong_authority, true)],
    );
    assert_rejected(
        &mollusk.process_instruction(&wrong_key, &[(wrong_authority, authority_account)]),
    );
}
