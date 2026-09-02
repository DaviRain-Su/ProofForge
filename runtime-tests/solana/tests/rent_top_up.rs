//! Mollusk matrix for `svm-sdk-001` rent top-up composition (`Examples.Svm.RentTopUp`).
//!
//! Covers: successful top-up+resize from an underfunded program-owned account, already-exempt
//! zero-deficit path, insufficient payer fail-closed, and view-independent top-up-only entry.

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
const DATA_LEN: usize = 16;
const TARGET_LEN: usize = 32;

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8]
        .try_into()
        .expect("8-byte discriminator")
}

fn layout_marker() -> u64 {
    let layout_sig = "1|0:dummy:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    u64::from_be_bytes(digest[..8].try_into().expect("layout marker"))
}

fn state_data(dummy: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    data[8..16].copy_from_slice(&dummy.to_le_bytes());
    data
}

fn program_so() -> PathBuf {
    PathBuf::from(env::var("PF_RENT_TOP_UP_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/RentTopUp.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(program_so()).unwrap_or_else(|e| panic!("read RentTopUp.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.sysvars.rent = Rent::with_lamports_per_byte(1_234);
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"rent-top-up-state").into())
}
fn data_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"rent-top-up-data").into())
}
fn payer_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"rent-top-up-payer").into())
}

fn state_account(program_id: &Pubkey, dummy: u64) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    account.data = state_data(dummy);
    account
}

fn data_account(program_id: &Pubkey, lamports: u64, space: usize) -> Account {
    Account::new(lamports, space, program_id)
}

fn payer_account(program_id: &Pubkey, lamports: u64) -> Account {
    Account::new(lamports, 0, program_id)
}

fn metas() -> Vec<AccountMeta> {
    vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(data_key(), false),
        AccountMeta::new(payer_key(), false),
    ]
}

fn ix(program_id: &Pubkey, name: &str) -> Instruction {
    Instruction::new_with_bytes(
        *program_id,
        &instruction_discriminator(name, 0),
        metas(),
    )
}

#[test]
fn grow_tops_up_underfunded_account_then_resizes() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let underfunded = required / 4;
    let payer_lamports = BASE_LAMPORTS;
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (data_key(), data_account(&program_id, underfunded, 8)),
        (payer_key(), payer_account(&program_id, payer_lamports)),
    ];
    let deficit = required.saturating_sub(underfunded);
    mollusk.process_and_validate_instruction(
        &ix(&program_id, "grow"),
        &accounts,
        &[
            Check::success(),
            Check::return_data(&(TARGET_LEN as u64).to_le_bytes()),
            Check::account(&data_key())
                .lamports(underfunded + deficit)
                .space(TARGET_LEN)
                .build(),
            Check::account(&payer_key())
                .lamports(payer_lamports - deficit)
                .build(),
            Check::account(&state_key()).data(&state_data(1)).build(),
        ],
    );
}

#[test]
fn grow_already_exempt_keeps_payer_balance() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let payer_lamports = BASE_LAMPORTS;
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (data_key(), data_account(&program_id, required, 8)),
        (payer_key(), payer_account(&program_id, payer_lamports)),
    ];
    mollusk.process_and_validate_instruction(
        &ix(&program_id, "grow"),
        &accounts,
        &[
            Check::success(),
            Check::return_data(&(TARGET_LEN as u64).to_le_bytes()),
            Check::account(&data_key())
                .lamports(required)
                .space(TARGET_LEN)
                .build(),
            Check::account(&payer_key()).lamports(payer_lamports).build(),
        ],
    );
}

#[test]
fn grow_insufficient_payer_fails_closed() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let underfunded = required / 4;
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (data_key(), data_account(&program_id, underfunded, 8)),
        (payer_key(), payer_account(&program_id, 1)),
    ];
    mollusk.process_and_validate_instruction(
        &ix(&program_id, "grow"),
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&data_key())
                .lamports(underfunded)
                .space(8)
                .build(),
            Check::account(&payer_key()).lamports(1).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn top_up_only_moves_exact_deficit() {
    let (program_id, mollusk) = harness();
    let required = mollusk.sysvars.rent.minimum_balance(TARGET_LEN);
    let underfunded = required / 3;
    let payer_lamports = BASE_LAMPORTS;
    let deficit = required.saturating_sub(underfunded);
    let accounts = vec![
        (state_key(), state_account(&program_id, 0)),
        (data_key(), data_account(&program_id, underfunded, 8)),
        (payer_key(), payer_account(&program_id, payer_lamports)),
    ];
    mollusk.process_and_validate_instruction(
        &ix(&program_id, "topUp"),
        &accounts,
        &[
            Check::success(),
            Check::return_data(&deficit.to_le_bytes()),
            Check::account(&data_key())
                .lamports(underfunded + deficit)
                .space(8)
                .build(),
            Check::account(&payer_key())
                .lamports(payer_lamports - deficit)
                .build(),
        ],
    );
}
