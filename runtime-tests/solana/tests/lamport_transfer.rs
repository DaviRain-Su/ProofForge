//! Focused Mollusk matrix for the checked SVM lamport-transfer effect
//! (`Examples.LamportTransfer`: vault = physical account 1, recipient = physical
//! account 2, state = physical account 0).
//!
//! Covers: successful debit/credit with zero total delta, the documented zero-amount
//! validated no-op, destination/source writable preflights, source current-program
//! ownership, insufficient balance, crediting overflow, duplicate Loader-v3 aliases
//! (same-canonical fails closed; alias of a distinct account resolves and succeeds),
//! reusable SDK account close/refund composition, and the atomic state/data/balance hold
//! on every failure.

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
/// State layout: layout marker word + one `moved` field.
const DATA_LEN: usize = 16;
const VAULT_BALANCE: u64 = 1_000_000;
const RECIPIENT_BALANCE: u64 = 500_000;
const VAULT_DATA: [u8; 8] = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88];

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8].try_into().expect("8-byte discriminator")
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

fn transfer_so() -> PathBuf {
    PathBuf::from(env::var("PF_LAMPORT_TRANSFER_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/LamportTransfer.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(transfer_so()).unwrap_or_else(|e| panic!("read LamportTransfer.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"lamport-transfer-state").into())
}

fn vault_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"lamport-transfer-vault").into())
}

fn recipient_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"lamport-transfer-recipient").into())
}

fn state_account(program_id: &Pubkey, moved: u64) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    account.data = state_data(moved);
    account
}

/// Program-owned vault funding every transfer.
fn vault_account(program_id: &Pubkey, lamports: u64) -> Account {
    let mut account = Account::new(lamports, VAULT_DATA.len(), program_id);
    account.data = VAULT_DATA.to_vec();
    account
}

/// Foreign-owned writable destination; the contract never requires self-ownership.
fn recipient_account(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::new_unique())
}

struct Fixture {
    state: (Pubkey, Account),
    vault: (Pubkey, Account),
    recipient: (Pubkey, Account),
}

fn fixture(program_id: &Pubkey) -> Fixture {
    Fixture {
        state: (state_key(), state_account(program_id, 0)),
        vault: (vault_key(), vault_account(program_id, VAULT_BALANCE)),
        recipient: (recipient_key(), recipient_account(RECIPIENT_BALANCE)),
    }
}

fn move_instruction(
    program_id: &Pubkey,
    name: &str,
    amount: u64,
    metas: Vec<AccountMeta>,
) -> Instruction {
    let disc = instruction_discriminator(name, 1);
    let mut data = disc.to_vec();
    data.extend_from_slice(&amount.to_le_bytes());
    Instruction::new_with_bytes(*program_id, &data, metas)
}

fn close_instruction(program_id: &Pubkey, metas: Vec<AccountMeta>) -> Instruction {
    Instruction::new_with_bytes(
        *program_id,
        &instruction_discriminator("closeVault", 0),
        metas,
    )
}

/// Standard metas/accounts: writable state, writable vault, writable recipient.
fn standard_metas() -> Vec<AccountMeta> {
    vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(recipient_key(), false),
    ]
}

fn standard_accounts(fixture: &Fixture) -> Vec<(Pubkey, Account)> {
    vec![
        fixture.state.clone(),
        fixture.vault.clone(),
        fixture.recipient.clone(),
    ]
}

#[test]
fn move_transfers_and_records_total() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let ix = move_instruction(&program_id, "move", 250_000, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::success(),
            Check::return_data(&250_000u64.to_le_bytes()),
            Check::account(&vault_key()).lamports(VAULT_BALANCE - 250_000).build(),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE + 250_000)
                .build(),
            Check::account(&state_key()).data(&state_data(250_000)).build(),
        ],
    );
}

#[test]
fn move_and_peek_reads_post_debit_balance() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let ix = move_instruction(&program_id, "moveAndPeek", 250_000, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::success(),
            Check::return_data(&(VAULT_BALANCE - 250_000).to_le_bytes()),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE + 250_000)
                .build(),
        ],
    );
}

#[test]
fn close_vault_shrinks_data_and_refunds_the_complete_balance() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let ix = close_instruction(&program_id, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::success(),
            Check::return_data(&VAULT_BALANCE.to_le_bytes()),
            Check::account(&vault_key()).lamports(0).data(&[]).build(),
            Check::account(&recipient_key())
                .lamports(RECIPIENT_BALANCE + VAULT_BALANCE)
                .build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn close_vault_destination_overflow_rolls_back_the_prior_resize() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let brimming = (recipient_key(), recipient_account(u64::MAX));
    let accounts = vec![fixture.state.clone(), fixture.vault.clone(), brimming];
    let ix = close_instruction(&program_id, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key())
                .lamports(VAULT_BALANCE)
                .data(&VAULT_DATA)
                .build(),
            Check::account(&recipient_key()).lamports(u64::MAX).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn close_vault_duplicate_refund_alias_rolls_back_the_prior_resize() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(vault_key(), false),
    ];
    let accounts = vec![
        fixture.state.clone(),
        fixture.vault.clone(),
        fixture.vault.clone(),
    ];
    let ix = close_instruction(&program_id, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key())
                .lamports(VAULT_BALANCE)
                .data(&VAULT_DATA)
                .build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn zero_amount_is_a_validated_noop() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let ix = move_instruction(&program_id, "move", 0, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn zero_amount_still_requires_writable_accounts() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    // Amount zero does not skip validation: a readonly destination fails closed.
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new_readonly(recipient_key(), false),
    ];
    let ix = move_instruction(&program_id, "move", 0, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn readonly_destination_fails_closed_without_writes() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new_readonly(recipient_key(), false),
    ];
    let ix = move_instruction(&program_id, "move", 100_000, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn readonly_vault_fails_closed_without_writes() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new_readonly(vault_key(), false),
        AccountMeta::new(recipient_key(), false),
    ];
    let ix = move_instruction(&program_id, "move", 100_000, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
        ],
    );
}

#[test]
fn foreign_owned_vault_fails_closed() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let foreign_vault = (vault_key(), recipient_account(VAULT_BALANCE));
    let accounts = vec![fixture.state.clone(), foreign_vault, fixture.recipient.clone()];
    let ix = move_instruction(&program_id, "move", 100_000, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn insufficient_vault_balance_fails_closed() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let ix = move_instruction(&program_id, "move", VAULT_BALANCE + 1, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &standard_accounts(&fixture),
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
        ],
    );
}

#[test]
fn destination_overflow_fails_closed() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let brimming = (recipient_key(), recipient_account(u64::MAX));
    let accounts = vec![fixture.state.clone(), fixture.vault.clone(), brimming];
    let ix = move_instruction(&program_id, "move", 1, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(u64::MAX).build(),
        ],
    );
}

#[test]
fn duplicate_alias_of_vault_as_recipient_fails_closed() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    // Loader-v3 encodes the repeated key as an 8-byte duplicate entry carrying the prior
    // position. The walk resolves position 2 to the vault's canonical header, so source
    // and destination share one canonical account and the transfer fails before writes.
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(vault_key(), false),
    ];
    let accounts = vec![
        fixture.state.clone(),
        fixture.vault.clone(),
        fixture.vault.clone(),
    ];
    let ix = move_instruction(&program_id, "move", 100_000, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn duplicate_alias_of_state_as_recipient_resolves_and_credits() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    // The recipient position duplicates the state account: the alias walk resolves the
    // position to the earlier canonical header, the canonical vault/state pointers differ,
    // and the credit lands on the state's lamports exactly once.
    let metas = vec![
        AccountMeta::new(state_key(), false),
        AccountMeta::new(vault_key(), false),
        AccountMeta::new(state_key(), false),
    ];
    let accounts = vec![
        fixture.state.clone(),
        fixture.vault.clone(),
        fixture.state.clone(),
    ];
    let ix = move_instruction(&program_id, "move", 100_000, metas);
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::success(),
            Check::return_data(&100_000u64.to_le_bytes()),
            Check::account(&vault_key()).lamports(VAULT_BALANCE - 100_000).build(),
            Check::account(&state_key())
                .lamports(BASE_LAMPORTS + 100_000)
                .data(&state_data(100_000))
                .build(),
        ],
    );
}

#[test]
fn moved_total_overflow_fails_before_any_transfer() {
    let (program_id, mollusk) = harness();
    let fixture = fixture(&program_id);
    let saturated = (state_key(), state_account(&program_id, u64::MAX));
    let accounts = vec![saturated, fixture.vault.clone(), fixture.recipient.clone()];
    let ix = move_instruction(&program_id, "move", 1, standard_metas());
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(4097)),
            Check::account(&vault_key()).lamports(VAULT_BALANCE).build(),
            Check::account(&recipient_key()).lamports(RECIPIENT_BALANCE).build(),
            Check::account(&state_key()).data(&state_data(u64::MAX)).build(),
        ],
    );
}
