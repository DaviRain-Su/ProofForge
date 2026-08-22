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
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const PEER_LAMPORTS: u64 = 3 * LAMPORTS_PER_SOL;
const PEER_DATA_LEN: usize = 24;

fn instruction_discriminator(name: &str, param_count: usize) -> String {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    let digest = Sha256::digest(preimage.as_bytes());
    hex::encode(digest)[..16].to_string()
}

fn discriminator_bytes(hex16: &str) -> [u8; 8] {
    let raw = hex::decode(hex16).expect("hex");
    let mut out = [0u8; 8];
    out.copy_from_slice(&raw);
    out
}

fn instruction_data(disc_hex: &str, params: &[u64]) -> Vec<u8> {
    let mut data = discriminator_bytes(disc_hex).to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    data
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("SOLANA_LEAN_PEER_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Peer.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Peer.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn peer_account(owner: &Pubkey, lamports: u64, data_len: usize) -> Account {
    Account::new(lamports, data_len, owner)
}

fn owner0_u64(owner: &Pubkey) -> u64 {
    let bytes = owner.to_bytes();
    u64::from_le_bytes(bytes[0..8].try_into().expect("8"))
}

fn build_ix(
    program_id: Pubkey,
    acc0: Pubkey,
    acc1: Pubkey,
    name: &str,
    writable1: bool,
    signer1: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, 0);
    let meta1 = if writable1 {
        AccountMeta::new(acc1, signer1)
    } else {
        AccountMeta::new_readonly(acc1, signer1)
    };
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![AccountMeta::new(acc0, false), meta1],
    )
}

fn view(name: &str, writable1: bool, signer1: bool, expect: u64) {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner = Pubkey::new_unique();
    let ix = build_ix(program_id, acc0, acc1, name, writable1, signer1);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, funded(BASE_LAMPORTS)),
            (acc1, peer_account(&owner, PEER_LAMPORTS, PEER_DATA_LEN)),
        ],
        &[
            Check::success(),
            Check::return_data(&expect.to_le_bytes()),
            Check::account(&acc1)
                .lamports(PEER_LAMPORTS)
                .owner(&owner)
                .space(PEER_DATA_LEN)
                .build(),
        ],
    );
}

#[test]
fn lamports1_returns_peer_balance() {
    view("lamports1", false, false, PEER_LAMPORTS);
}

#[test]
fn owner1_returns_first_u64() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner = Pubkey::new_unique();
    let ix = build_ix(program_id, acc0, acc1, "owner1", false, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, funded(BASE_LAMPORTS)),
            (acc1, peer_account(&owner, PEER_LAMPORTS, PEER_DATA_LEN)),
        ],
        &[
            Check::success(),
            Check::return_data(&owner0_u64(&owner).to_le_bytes()),
        ],
    );
}

#[test]
fn data_len1_returns_24() {
    view("dataLen1", false, false, PEER_DATA_LEN as u64);
}

#[test]
fn signer1_flag_tracks_meta() {
    view("signer1", false, true, 1);
    view("signer1", false, false, 0);
}

#[test]
fn writable1_flag_tracks_meta() {
    view("writable1", true, false, 1);
    view("writable1", false, false, 0);
}

#[test]
fn executable1_flag_is_zero_for_data_account() {
    view("executable1", false, false, 0);
}

#[test]
fn missing_second_account_fails() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let disc = instruction_discriminator("lamports1", 0);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![AccountMeta::new(acc0, false)],
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[(acc0, funded(BASE_LAMPORTS))],
        &[Check::err(ProgramError::Custom(1))],
    );
}
