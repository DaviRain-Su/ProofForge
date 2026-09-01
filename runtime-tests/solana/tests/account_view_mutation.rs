//! Focused Mollusk matrix for `svm-rt-003` (`Examples.AccountViewMutation`):
//! AccountView + checked lamport mutation on the same static account prefix.
//!
//! Covers: view read, transfer+view peek, readonly/same-canonical fail-closed,
//! Loader-v3 backward alias in the variable tail (resolves), and view index OOB.

mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const DATA_LEN: usize = 16;
const VAULT_BALANCE: u64 = 1_000_000;
const RECIPIENT_BALANCE: u64 = 500_000;
const VAULT_DATA: [u8; 8] = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88];

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8]
        .try_into()
        .expect("8-byte discriminator")
}

fn layout_marker() -> u64 {
    let layout_sig = "1|0:moved:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    u64::from_be_bytes(digest[..8].try_into().expect("layout marker"))
}

fn state_data(moved: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    data[8..16].copy_from_slice(&moved.to_le_bytes());
    data
}

fn program_so() -> PathBuf {
    PathBuf::from(env::var("PF_ACCOUNT_VIEW_MUTATION_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/AccountViewMutation.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(program_so()).unwrap_or_else(|e| {
        panic!("read AccountViewMutation.so: {e}")
    });
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"account-view-mutation-state").into())
}

fn vault_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"account-view-mutation-vault").into())
}

fn recipient_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"account-view-mutation-recipient").into())
}

fn state_account(program_id: &Pubkey, moved: u64) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    account.data = state_data(moved);
    account
}

fn vault_account(program_id: &Pubkey, lamports: u64) -> Account {
    let mut account = Account::new(lamports, VAULT_DATA.len(), program_id);
    account.data = VAULT_DATA.to_vec();
    account
}

fn recipient_account(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::new_unique())
}

fn standard_metas() -> Vec<AccountMeta> {
    vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(recipient_key(), false),
    ]
}

fn standard_accounts(program_id: &Pubkey) -> Vec<(Pubkey, Account)> {
    vec![
        (state_key(), state_account(program_id, 0)),
        (vault_key(), vault_account(program_id, VAULT_BALANCE)),
        (recipient_key(), recipient_account(RECIPIENT_BALANCE)),
    ]
}

fn ix(program_id: &Pubkey, name: &str, params: &[u64], metas: Vec<AccountMeta>) -> Instruction {
    let mut data = instruction_discriminator(name, params.len()).to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    Instruction::new_with_bytes(*program_id, &data, metas)
}

#[test]
fn peek_vault_reads_through_view() {
    let (program_id, mollusk) = harness();
    let instruction = ix(&program_id, "peekVault", &[0], standard_metas());
    mollusk.process_and_validate_instruction(
        &instruction,
        &standard_accounts(&program_id),
        &[
            Check::success(),
            Check::return_data(&VAULT_BALANCE.to_le_bytes()),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
        ],
    );
}

#[test]
fn move_and_peek_transfers_then_reads_post_debit_via_view() {
    let (program_id, mollusk) = harness();
    let amount = 250_000u64;
    let instruction = ix(&program_id, "moveAndPeek", &[amount, 0], standard_metas());
    mollusk.process_and_validate_instruction(
        &instruction,
        &standard_accounts(&program_id),
        &[
            Check::success(),
            Check::return_data(&(VAULT_BALANCE - amount).to_le_bytes()),
            Check::account(&vault_key())
                .lamports(VAULT_BALANCE - amount)
                .build(),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE + amount)
                .build(),
            Check::account(&state_key()).data(&state_data(amount)).build(),
        ],
    );
}

#[test]
fn move_and_peek_readonly_vault_fails_closed() {
    let (program_id, mollusk) = harness();
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new_readonly(vault_key(), false),
        AccountMeta::new(recipient_key(), false),
    ];
    let instruction = ix(&program_id, "moveAndPeek", &[1, 0], metas);
    mollusk.process_and_validate_instruction(
        &instruction,
        &standard_accounts(&program_id),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE)
                .build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn move_and_peek_same_canonical_alias_fails_closed() {
    let (program_id, mollusk) = harness();
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(vault_key(), false),
    ];
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (vault_key(), vault_account(&program_id, VAULT_BALANCE)),
        (vault_key(), vault_account(&program_id, VAULT_BALANCE)),
    ];
    let instruction = ix(&program_id, "moveAndPeek", &[1, 0], metas);
    mollusk.process_and_validate_instruction(
        &instruction,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn variable_tail_alias_of_vault_still_transfers() {
    let (program_id, mollusk) = harness();
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(recipient_key(), false),
        AccountMeta::new(vault_key(), false),
    ];
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (vault_key(), vault_account(&program_id, VAULT_BALANCE)),
        (recipient_key(), recipient_account(RECIPIENT_BALANCE)),
        (vault_key(), vault_account(&program_id, VAULT_BALANCE)),
    ];
    let amount = 100_000u64;
    let instruction = ix(&program_id, "moveAndPeek", &[amount, 0], metas);
    mollusk.process_and_validate_instruction(
        &instruction,
        &accounts,
        &[
            Check::success(),
            Check::return_data(&(VAULT_BALANCE - amount).to_le_bytes()),
            Check::account(&vault_key())
                .lamports(VAULT_BALANCE - amount)
                .build(),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE + amount)
                .build(),
        ],
    );
}

#[test]
fn peek_vault_index_oob_fails_closed() {
    let (program_id, mollusk) = harness();
    let instruction = ix(&program_id, "peekVault", &[2], standard_metas());
    mollusk.process_and_validate_instruction(
        &instruction,
        &standard_accounts(&program_id),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}
