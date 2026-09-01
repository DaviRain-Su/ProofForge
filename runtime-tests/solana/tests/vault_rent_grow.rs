//! Mollusk matrix for `svm-sdk-001` second consumer (`Examples.VaultRentGrow`).

mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const STATE_LEN: usize = 16;
const TARGET_LEN: usize = 64;

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8]
        .try_into()
        .expect("8-byte discriminator")
}

fn layout_marker() -> u64 {
    let layout_sig = "1|0:grown:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    u64::from_be_bytes(digest[..8].try_into().expect("layout marker"))
}

fn state_data(grown: u64) -> Vec<u8> {
    let mut data = vec![0u8; STATE_LEN];
    data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    data[8..16].copy_from_slice(&grown.to_le_bytes());
    data
}

fn program_so() -> PathBuf {
    PathBuf::from(env::var("PF_VAULT_RENT_GROW_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/VaultRentGrow.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(program_so()).unwrap_or_else(|e| panic!("read VaultRentGrow.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.sysvars.rent = Rent::with_lamports_per_byte(2_000);
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"vault-rent-grow-state").into())
}
fn vault_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"vault-rent-grow-vault").into())
}
fn fund_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"vault-rent-grow-fund").into())
}

fn state_account(program_id: &Pubkey, grown: u64) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, STATE_LEN, program_id);
    account.data = state_data(grown);
    account
}

fn vault_account(program_id: &Pubkey, lamports: u64, space: usize) -> Account {
    Account::new(lamports, space, program_id)
}

fn fund_account(program_id: &Pubkey, lamports: u64) -> Account {
    Account::new(lamports, 0, program_id)
}

fn metas() -> Vec<AccountMeta> {
    vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(fund_key(), false),
    ]
}

fn ix(program_id: &Pubkey) -> Instruction {
    Instruction::new_with_bytes(
        *program_id,
        &instruction_discriminator("grow", 0),
        metas(),
    )
}

#[test]
fn grow_tops_up_vault_then_resizes() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let underfunded = required / 5;
    let fund_lamports = BASE_LAMPORTS;
    let deficit = required.saturating_sub(underfunded);
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (vault_key(), vault_account(&program_id, underfunded, 8)),
        (fund_key(), fund_account(&program_id, fund_lamports)),
    ];
    mollusk.process_and_validate_instruction(
        &ix(&program_id),
        &accounts,
        &[
            Check::success(),
            Check::return_data(&(TARGET_LEN as u64).to_le_bytes()),
            Check::account(&vault_key())
                .lamports(underfunded + deficit)
                .space(TARGET_LEN)
                .build(),
            Check::account(&fund_key())
                .lamports(fund_lamports - deficit)
                .build(),
            Check::account(&state_key()).data(&state_data(1)).build(),
        ],
    );
}

#[test]
fn grow_insufficient_fund_fails_closed() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let underfunded = required / 5;
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (vault_key(), vault_account(&program_id, underfunded, 8)),
        (fund_key(), fund_account(&program_id, 1)),
    ];
    mollusk.process_and_validate_instruction(
        &ix(&program_id),
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key())
                .lamports(underfunded)
                .space(8)
                .build(),
            Check::account(&fund_key()).lamports(1).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}
