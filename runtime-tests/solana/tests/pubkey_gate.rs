//! Focused Mollusk matrix for the first-class SVM SDK `Pubkey` value via the independent
//! `Examples.PubkeyGate` consumer (state = physical account 0, authority = 1, peer = 2,
//! program = 3).
//!
//! Covers: fixed-key equality and mismatch in each of the four little-endian words (including
//! differences outside word0), a runtime-supplied key built once from four scalar words,
//! account-to-account key equality/inequality, owner-vs-key and owner-vs-constant matching,
//! canonical executable+key+owner authentication, the fail-closed gated mutation with atomic
//! state hold, and the static four-account geometry. The program performs no allocation: every
//! comparison runs in place against walked Loader-v3 account headers.

mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
/// State layout: layout marker word + one `accepted` field.
const DATA_LEN: usize = 16;

/// `SHA-256("pubkey-gate-authority")`: the fixed 32-byte authority key compiled into the
/// program as four little-endian words.
const AUTHORITY_KEY: [u8; 32] = [
    0x0a, 0x16, 0x24, 0x47, 0xdd, 0x9f, 0x8c, 0x3c, 0x38, 0x00, 0x72, 0x25, 0xae, 0x6c, 0xd6,
    0x61, 0xe2, 0x39, 0x18, 0x2f, 0xf1, 0x7e, 0xa2, 0x26, 0x35, 0xca, 0x1d, 0x7d, 0x29, 0x10,
    0x4a, 0x82,
];
/// `SHA-256("pubkey-gate-owner")`: the fixed 32-byte expected owner.
const OWNER_KEY: [u8; 32] = [
    0x95, 0xbb, 0xc7, 0x96, 0x60, 0x72, 0xc3, 0x7f, 0x53, 0x56, 0x06, 0x1c, 0x3e, 0x6b, 0xbc,
    0x4f, 0x33, 0x26, 0x10, 0xeb, 0x15, 0xef, 0x87, 0x22, 0x10, 0x82, 0xfa, 0x54, 0x3c, 0x87,
    0x4a, 0x9f,
];

fn authority() -> Pubkey {
    Pubkey::new_from_array(AUTHORITY_KEY)
}

fn owner_key() -> Pubkey {
    Pubkey::new_from_array(OWNER_KEY)
}

/// The same 32-byte key with one bit flipped inside little-endian word `word` (0..=3).
fn key_with_word_flipped(key: &Pubkey, word: usize) -> Pubkey {
    let mut bytes: [u8; 32] = key.to_bytes();
    bytes[word * 8] ^= 0x01;
    Pubkey::new_from_array(bytes)
}

fn word_u64(key: &Pubkey, word: usize) -> u64 {
    let off = word * 8;
    u64::from_le_bytes(key.to_bytes()[off..off + 8].try_into().expect("8"))
}

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8]
        .try_into()
        .expect("8-byte discriminator")
}

fn layout_marker() -> u64 {
    let layout_sig = "1|0:accepted:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    u64::from_be_bytes(digest[..8].try_into().expect("layout marker"))
}

fn state_data(accepted: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    data[8..16].copy_from_slice(&accepted.to_le_bytes());
    data
}

fn gate_so() -> std::path::PathBuf {
    std::path::PathBuf::from(std::env::var("PF_PUBKEY_GATE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/PubkeyGate.so",
            std::env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf =
        std::fs::read(gate_so()).unwrap_or_else(|e| panic!("read PubkeyGate.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"pubkey-gate-state").into())
}

fn peer_key() -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(b"pubkey-gate-peer").into())
}

fn state_account(program_id: &Pubkey, accepted: u64) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    account.data = state_data(accepted);
    account
}

/// Plain non-executable account with the given owner.
fn plain_account(owner: &Pubkey) -> Account {
    Account::new(BASE_LAMPORTS, 0, owner)
}

/// Executable program account carrying the fixed expected-owner key.
fn executable_program_account() -> Account {
    let mut account = Account::new(BASE_LAMPORTS, 0, &Pubkey::new_unique());
    account.executable = true;
    account
}

/// Standard fixture: authority key equals the fixed key, authority owner equals the peer key,
/// program account is non-executable with a fresh key. Tests override what they exercise.
struct Fixture {
    authority: (Pubkey, Account),
    peer: (Pubkey, Account),
    program: (Pubkey, Account),
}

fn fixture() -> Fixture {
    let peer = peer_key();
    Fixture {
        authority: (authority(), plain_account(&peer)),
        peer: (peer, plain_account(&Pubkey::new_unique())),
        program: (Pubkey::new_unique(), plain_account(&Pubkey::new_unique())),
    }
}

fn metas(authority: &Pubkey, peer: &Pubkey, program: &Pubkey, writable_state: bool) -> Vec<AccountMeta> {
    let state = if writable_state {
        AccountMeta::new(state_key(), false)
    } else {
        AccountMeta::new_readonly(state_key(), false)
    };
    vec![
        state,
        AccountMeta::new_readonly(*authority, false),
        AccountMeta::new_readonly(*peer, false),
        AccountMeta::new_readonly(*program, false),
    ]
}

fn accounts(
    program_id: &Pubkey,
    fixture: &Fixture,
    accepted: u64,
) -> Vec<(Pubkey, Account)> {
    vec![
        (state_key(), state_account(program_id, accepted)),
        fixture.authority.clone(),
        fixture.peer.clone(),
        fixture.program.clone(),
    ]
}

fn view_instruction(
    program_id: &Pubkey,
    name: &str,
    params: &[u64],
    metas: Vec<AccountMeta>,
) -> Instruction {
    let disc = instruction_discriminator(name, params.len());
    let mut data = disc.to_vec();
    for param in params {
        data.extend_from_slice(&param.to_le_bytes());
    }
    Instruction::new_with_bytes(*program_id, &data, metas)
}

/// Run a read-only view and require the exact 0/1 return data.
fn expect_view(name: &str, params: &[u64], fixture: &Fixture, expected: u64) {
    let (program_id, mollusk) = harness();
    let f = fixture;
    let ix = view_instruction(
        &program_id,
        name,
        params,
        metas(&f.authority.0, &f.peer.0, &f.program.0, false),
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts(&program_id, f, 0),
        &[Check::success(), Check::return_data(&expected.to_le_bytes())],
    );
}

#[test]
fn authority_matches_exact_fixed_key() {
    expect_view("authorityMatches", &[], &fixture(), 1);
}

#[test]
fn authority_mismatch_in_word0_fails() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 0), plain_account(&peer_key()));
    expect_view("authorityMatches", &[], &f, 0);
}

#[test]
fn authority_mismatch_in_word1_fails() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 1), plain_account(&peer_key()));
    expect_view("authorityMatches", &[], &f, 0);
}

#[test]
fn authority_mismatch_in_word2_fails() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 2), plain_account(&peer_key()));
    expect_view("authorityMatches", &[], &f, 0);
}

#[test]
fn authority_mismatch_in_word3_fails() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 3), plain_account(&peer_key()));
    expect_view("authorityMatches", &[], &f, 0);
}

#[test]
fn supplied_key_matches_exactly() {
    let params: Vec<u64> = (0..4).map(|w| word_u64(&authority(), w)).collect();
    expect_view("suppliedMatches", &params, &fixture(), 1);
}

#[test]
fn supplied_key_mismatch_in_word2_fails() {
    let mut params: Vec<u64> = (0..4).map(|w| word_u64(&authority(), w)).collect();
    params[2] ^= 1;
    expect_view("suppliedMatches", &params, &fixture(), 0);
}

#[test]
fn supplied_key_mismatch_in_word3_fails() {
    let mut params: Vec<u64> = (0..4).map(|w| word_u64(&authority(), w)).collect();
    params[3] ^= 1;
    expect_view("suppliedMatches", &params, &fixture(), 0);
}

#[test]
fn peer_key_value_rejected_when_word1_differs() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&peer_key(), 1), plain_account(&peer_key()));
    expect_view("peerKeyAccepted", &[], &f, 0);
    expect_view("keysEqual", &[], &f, 0);
}

#[test]
fn equal_keys_across_positions_fail_closed_as_duplicate_aliases() {
    // Two positions naming the same key are Loader-v3 duplicate aliases of one account. The
    // walked ABI rejects duplicates before the method body, so complete-key equality between
    // two positions is a fail-closed `Custom(1)`, never a silent `1`.
    let (program_id, mollusk) = harness();
    let shared = peer_key();
    let f = Fixture {
        authority: (shared, plain_account(&Pubkey::new_unique())),
        peer: (shared, plain_account(&Pubkey::new_unique())),
        program: (Pubkey::new_unique(), plain_account(&Pubkey::new_unique())),
    };
    for name in ["keysEqual", "peerKeyAccepted"] {
        let ix = view_instruction(
            &program_id,
            name,
            &[],
            metas(&f.authority.0, &f.peer.0, &f.program.0, false),
        );
        mollusk.process_and_validate_instruction(
            &ix,
            &accounts(&program_id, &f, 0),
            &[Check::err(ProgramError::Custom(1))],
        );
    }
}

#[test]
fn keys_equal_fails_on_word3_difference() {
    let mut f = fixture();
    f.authority = (authority(), plain_account(&peer_key()));
    f.peer = (key_with_word_flipped(&authority(), 3), plain_account(&Pubkey::new_unique()));
    expect_view("keysEqual", &[], &f, 0);
}

#[test]
fn key_differs_reports_zero_for_exact_key() {
    expect_view("keyDiffers", &[], &fixture(), 0);
}

#[test]
fn key_differs_reports_one_for_word1_difference() {
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 1), plain_account(&peer_key()));
    expect_view("keyDiffers", &[], &f, 1);
}

#[test]
fn owner_is_peer_key_when_owner_equals_peer_key() {
    // Standard fixture: authority owner = peer key.
    expect_view("ownerIsPeerKey", &[], &fixture(), 1);
}

#[test]
fn owner_is_peer_key_fails_on_word2_difference() {
    let mut f = fixture();
    let wrong_owner = key_with_word_flipped(&peer_key(), 2);
    f.authority = (authority(), plain_account(&wrong_owner));
    expect_view("ownerIsPeerKey", &[], &f, 0);
}

#[test]
fn owner_matches_exact_fixed_owner() {
    let mut f = fixture();
    f.authority = (authority(), plain_account(&owner_key()));
    expect_view("ownerMatches", &[], &f, 1);
}

#[test]
fn owner_mismatch_in_word1_fails() {
    let mut f = fixture();
    let wrong_owner = key_with_word_flipped(&owner_key(), 1);
    f.authority = (authority(), plain_account(&wrong_owner));
    expect_view("ownerMatches", &[], &f, 0);
}

#[test]
fn owner_authenticated_by_executable_program_key() {
    // Canonical matching: program account executable, its complete key equals the fixed
    // expected owner, and the authority's complete owner equals the program's key.
    let mut f = fixture();
    f.authority = (authority(), plain_account(&owner_key()));
    f.program = (owner_key(), executable_program_account());
    expect_view("ownerAuthenticated", &[], &f, 1);
}

#[test]
fn owner_authentication_requires_executable_flag() {
    let mut f = fixture();
    f.authority = (authority(), plain_account(&owner_key()));
    f.program = (owner_key(), plain_account(&Pubkey::new_unique()));
    expect_view("ownerAuthenticated", &[], &f, 0);
}

#[test]
fn owner_authentication_fails_on_program_key_word3_difference() {
    let mut f = fixture();
    let wrong_program = key_with_word_flipped(&owner_key(), 3);
    f.authority = (authority(), plain_account(&wrong_program));
    f.program = (wrong_program, executable_program_account());
    expect_view("ownerAuthenticated", &[], &f, 0);
}

#[test]
fn accept_authorized_increments_and_returns_count() {
    let (program_id, mollusk) = harness();
    let f = fixture();
    let ix = view_instruction(
        &program_id,
        "accept",
        &[],
        metas(&f.authority.0, &f.peer.0, &f.program.0, true),
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts(&program_id, &f, 7),
        &[
            Check::success(),
            Check::return_data(&8u64.to_le_bytes()),
            Check::account(&state_key()).data(&state_data(8)).build(),
        ],
    );
}

#[test]
fn accept_rejected_on_word3_mismatch_without_state_change() {
    let (program_id, mollusk) = harness();
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 3), plain_account(&peer_key()));
    let ix = view_instruction(
        &program_id,
        "accept",
        &[],
        metas(&f.authority.0, &f.peer.0, &f.program.0, true),
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts(&program_id, &f, 7),
        &[
            Check::err(ProgramError::Custom(4098)),
            Check::account(&state_key()).data(&state_data(7)).build(),
        ],
    );
}

#[test]
fn accept_rejected_on_word0_mismatch_without_state_change() {
    let (program_id, mollusk) = harness();
    let mut f = fixture();
    f.authority = (key_with_word_flipped(&authority(), 0), plain_account(&peer_key()));
    let ix = view_instruction(
        &program_id,
        "accept",
        &[],
        metas(&f.authority.0, &f.peer.0, &f.program.0, true),
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts(&program_id, &f, 7),
        &[
            Check::err(ProgramError::Custom(4098)),
            Check::account(&state_key()).data(&state_data(7)).build(),
        ],
    );
}

#[test]
fn static_geometry_rejects_missing_accounts() {
    // The contract names exactly four static accounts; a truncated invocation fails closed
    // before any key word is read.
    let (program_id, mollusk) = harness();
    let f = fixture();
    let ix = view_instruction(
        &program_id,
        "authorityMatches",
        &[],
        vec![
            AccountMeta::new_readonly(state_key(), false),
            AccountMeta::new_readonly(f.authority.0, false),
            AccountMeta::new_readonly(f.peer.0, false),
        ],
    );
    let keyed = vec![
        (state_key(), state_account(&program_id, 0)),
        f.authority.clone(),
        f.peer.clone(),
    ];
    mollusk.process_and_validate_instruction(
        &ix,
        &keyed,
        &[Check::err(ProgramError::Custom(1))],
    );
}
