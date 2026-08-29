//! Focused Mollusk matrix for the SVM-RT-1 bounded remaining-account view
//! (`Examples.AccountView`, compile-time window = physical accounts 1..4).
//!
//! Covers: selected data/header reads, capacity OOB, available-count OOB, duplicate
//! account keys, short data, signer/writable/owner flags, and the atomic state hold
//! on a failed view access.

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
/// State layout: layout marker word + one `value` field.
const DATA_LEN: usize = 16;

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8].try_into().expect("8-byte discriminator")
}

fn instruction_data(disc: [u8; 8], params: &[u64]) -> Vec<u8> {
    let mut data = disc.to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    data
}

fn layout_marker() -> u64 {
    let layout_sig = "1|0:count:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    u64::from_be_bytes(digest[..8].try_into().expect("layout marker"))
}

fn state_data(value: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    data[8..16].copy_from_slice(&value.to_le_bytes());
    data
}

fn view_so() -> PathBuf {
    PathBuf::from(env::var("PF_ACCOUNT_VIEW_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/AccountView.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(view_so()).unwrap_or_else(|e| panic!("read AccountView.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

/// One remaining account with four distinct u64 data words.
fn data_account(owner: &Pubkey, base: u64, lamports: u64) -> Account {
    let mut account = Account::new(lamports, 32, owner);
    for i in 0..4u64 {
        let off = (i * 8) as usize;
        account.data[off..off + 8].copy_from_slice(&(base + i).to_le_bytes());
    }
    account
}

fn readonly(key: &Pubkey, signer: bool) -> AccountMeta {
    AccountMeta::new_readonly(*key, signer)
}

fn writable(key: &Pubkey) -> AccountMeta {
    AccountMeta::new(*key, false)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"account-view-state").into())
}

/// Peek one u64 view result from the selected remaining account.
fn expect_return(
    program_id: &Pubkey,
    mollusk: &Mollusk,
    name: &str,
    params: &[u64],
    state: &Account,
    metas: Vec<AccountMeta>,
    accounts: Vec<(Pubkey, Account)>,
    expected: u64,
) {
    let disc = instruction_discriminator(name, params.len());
    let mut full_metas = vec![AccountMeta::new_readonly(state_key(), false)];
    full_metas.extend(metas);
    let ix = Instruction::new_with_bytes(*program_id, &instruction_data(disc, params), full_metas);
    let mut full_accounts = vec![(state_key(), state.clone())];
    full_accounts.extend(accounts);
    mollusk.process_and_validate_instruction(
        &ix,
        &full_accounts,
        &[Check::success(), Check::return_data(&expected.to_le_bytes())],
    );
}

fn expect_custom_one(
    program_id: &Pubkey,
    mollusk: &Mollusk,
    name: &str,
    params: &[u64],
    state: &Account,
    metas: Vec<AccountMeta>,
    accounts: Vec<(Pubkey, Account)>,
) {
    let disc = instruction_discriminator(name, params.len());
    let mut full_metas = vec![AccountMeta::new_readonly(state_key(), false)];
    full_metas.extend(metas);
    let ix = Instruction::new_with_bytes(*program_id, &instruction_data(disc, params), full_metas);
    let mut full_accounts = vec![(state_key(), state.clone())];
    full_accounts.extend(accounts);
    mollusk.process_and_validate_instruction(
        &ix,
        &full_accounts,
        &[Check::err(ProgramError::Custom(1))],
    );
}

/// Standard full-window fixture: state + 4 remaining accounts with distinct words,
/// lamports, and ownership. Accounts 1+0 and 1+1 are signer/writable as requested.
fn full_window(
    program_id: &Pubkey,
) -> (Account, Vec<(Pubkey, Account)>, Vec<AccountMeta>) {
    let mut state = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    state.data = state_data(0);
    let mut accounts = Vec::new();
    let mut metas = Vec::new();
    for i in 0..4u64 {
        let key = Pubkey::new_from_array(Sha256::digest(format!("view-acc-{i}").as_bytes()).into());
        let owner = if i == 2 { program_id } else { &Pubkey::new_unique() };
        accounts.push((key, data_account(owner, 100 * (i + 1), 1000 * (i + 1))));
        let (signer, writable_flag) = match i {
            0 => (false, true),
            1 => (true, false),
            _ => (false, false),
        };
        metas.push(if writable_flag {
            if signer {
                AccountMeta::new(key, true)
            } else {
                writable(&key)
            }
        } else {
            readonly(&key, signer)
        });
    }
    (state, accounts, metas)
}

#[test]
fn peek_data_words_follow_runtime_index() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    for (index, base) in [(0u64, 100u64), (1, 200), (2, 300), (3, 400)] {
        expect_return(
            &program_id,
            &mollusk,
            "peek",
            &[index],
            &state,
            metas.clone(),
            accounts.clone(),
            base,
        );
        expect_return(
            &program_id,
            &mollusk,
            "peekWord1",
            &[index],
            &state,
            metas.clone(),
            accounts.clone(),
            base + 1,
        );
    }
}

#[test]
fn fixed_prefix_compare_uses_exact_memcmp_bits() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    let expected = u64::from((-1i32) as u32);
    expect_return(
        &program_id,
        &mollusk,
        "comparePrefixes",
        &[],
        &state,
        metas,
        accounts,
        expected,
    );
}

#[test]
fn selected_word_round_trips_through_transient_vector() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    expect_return(
        &program_id,
        &mollusk,
        "stageSelected",
        &[2],
        &state,
        metas,
        accounts,
        300,
    );
}

#[test]
fn selected_word_low_byte_round_trips_through_transient_bytes() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    let selected = 300u64;
    expect_return(
        &program_id,
        &mollusk,
        "stageSelectedBytes",
        &[2],
        &state,
        metas,
        accounts,
        selected & 0xff,
    );
}

#[test]
fn peek_key_follows_runtime_index() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    for (index, (key, _)) in accounts.iter().enumerate() {
        let word = u64::from_le_bytes(key.as_ref()[0..8].try_into().expect("key word"));
        expect_return(
            &program_id,
            &mollusk,
            "peekKey",
            &[index as u64],
            &state,
            metas.clone(),
            accounts.clone(),
            word,
        );
    }
}

#[test]
fn signer_and_writable_flags_follow_metas() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    // Account 1+0: writable, not signer. Account 1+1: signer, not writable.
    expect_return(
        &program_id,
        &mollusk,
        "peekSigner",
        &[0],
        &state,
        metas.clone(),
        accounts.clone(),
        0,
    );
    expect_return(
        &program_id,
        &mollusk,
        "peekSigner",
        &[1],
        &state,
        metas.clone(),
        accounts.clone(),
        1,
    );
    expect_return(
        &program_id,
        &mollusk,
        "peekWritable",
        &[0],
        &state,
        metas.clone(),
        accounts.clone(),
        1,
    );
    expect_return(
        &program_id,
        &mollusk,
        "peekWritable",
        &[1],
        &state,
        metas.clone(),
        accounts.clone(),
        0,
    );
}

#[test]
fn lamports_data_len_and_owner_follow_selected_account() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    for i in 0..4u64 {
        expect_return(
            &program_id,
            &mollusk,
            "peekLamports",
            &[i],
            &state,
            metas.clone(),
            accounts.clone(),
            1000 * (i + 1),
        );
        expect_return(
            &program_id,
            &mollusk,
            "peekDataLen",
            &[i],
            &state,
            metas.clone(),
            accounts.clone(),
            32,
        );
        // Account 1+2 is program-owned; every other window account is foreign.
        expect_return(
            &program_id,
            &mollusk,
            "peekOwned",
            &[i],
            &state,
            metas.clone(),
            accounts.clone(),
            if i == 2 { 0 } else { 1 },
        );
    }
}

#[test]
fn capacity_oob_fails_atomically() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    // index 4 is outside the compile-time capacity 4 even though 5 accounts exist.
    expect_custom_one(
        &program_id,
        &mollusk,
        "peek",
        &[4],
        &state,
        metas.clone(),
        accounts.clone(),
    );
    expect_custom_one(
        &program_id,
        &mollusk,
        "peekKey",
        &[4],
        &state,
        metas.clone(),
        accounts.clone(),
    );
}

#[test]
fn available_count_oob_fails_atomically() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    // Variable remaining accounts: only three of the four window accounts are supplied, so
    // the static prefix walk cannot locate instruction data; the runtime account-count
    // gate must reject the access without reading any bytes.
    expect_custom_one(
        &program_id,
        &mollusk,
        "peek",
        &[3],
        &state,
        metas[..3].to_vec(),
        accounts[..3].to_vec(),
    );
}

#[test]
fn duplicate_account_keys_fail_closed_on_the_walk_marker() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    // Loader-v3 encodes a repeated key as a one-byte NON_DUP_MARKER entry carrying the
    // original position instead of an 88-byte header. The walk contract verifies the 0xff
    // marker byte of every traversed account, so a duplicate inside the window is rejected
    // atomically before any byte is read; no wrong account bytes can be returned.
    let dup_accounts = vec![
        (accounts[0].0, accounts[0].1.clone()),
        (accounts[1].0, accounts[1].1.clone()),
        (accounts[2].0, accounts[2].1.clone()),
        (accounts[2].0, accounts[2].1.clone()),
    ];
    let dup_metas = vec![
        metas[0].clone(),
        metas[1].clone(),
        metas[2].clone(),
        readonly(&accounts[2].0, false),
    ];
    expect_custom_one(
        &program_id,
        &mollusk,
        "peek",
        &[3],
        &state,
        dup_metas,
        dup_accounts,
    );
}

#[test]
fn short_data_fails_atomically() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    // The selected account has 4 data bytes: the u64 word read must not go past data_len.
    let mut short = Account::new(BASE_LAMPORTS, 4, &Pubkey::new_unique());
    short.data.copy_from_slice(&[1, 2, 3, 4]);
    let short_accounts = vec![
        (accounts[0].0, short),
        (accounts[1].0, accounts[1].1.clone()),
        (accounts[2].0, accounts[2].1.clone()),
        (accounts[3].0, accounts[3].1.clone()),
    ];
    expect_custom_one(
        &program_id,
        &mollusk,
        "peek",
        &[0],
        &state,
        metas.clone(),
        short_accounts,
    );
}

#[test]
fn absorb_commits_selected_word_and_delta() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    let disc = instruction_discriminator("absorb", 2);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(disc, &[0, 5]),
        vec![writable(&state_key())]
            .into_iter()
            .chain(metas.iter().cloned())
            .collect(),
    );
    let mut full_accounts = vec![(state_key(), state.clone())];
    full_accounts.extend(accounts);
    let mut expected = state_data(0);
    expected[8..16].copy_from_slice(&105u64.to_le_bytes());
    mollusk.process_and_validate_instruction(
        &ix,
        &full_accounts,
        &[
            Check::success(),
            Check::return_data(&105u64.to_le_bytes()),
            Check::account(&state_key()).data(&expected).build(),
        ],
    );
}

#[test]
fn absorb_oob_holds_state_atomically() {
    let (program_id, mollusk) = harness();
    let (state, accounts, metas) = full_window(&program_id);
    let disc = instruction_discriminator("absorb", 2);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(disc, &[4, 5]),
        vec![writable(&state_key())]
            .into_iter()
            .chain(metas.iter().cloned())
            .collect(),
    );
    let mut full_accounts = vec![(state_key(), state.clone())];
    full_accounts.extend(accounts);
    mollusk.process_and_validate_instruction(
        &ix,
        &full_accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&state_key()).data(&state_data(0)).build(),
        ],
    );
}

#[test]
fn initialize_writes_marker_and_value_over_full_window() {
    let (program_id, mollusk) = harness();
    let (_, accounts, metas) = full_window(&program_id);
    let state = Account::new(BASE_LAMPORTS, DATA_LEN, &program_id);
    let disc = instruction_discriminator("initialize", 1);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(disc, &[9]),
        vec![writable(&state_key())].into_iter().chain(metas).collect(),
    );
    let mut full_accounts = vec![(state_key(), state)];
    full_accounts.extend(accounts);
    mollusk.process_and_validate_instruction(
        &ix,
        &full_accounts,
        &[
            Check::success(),
            Check::account(&state_key()).data(&state_data(9)).build(),
        ],
    );
}
