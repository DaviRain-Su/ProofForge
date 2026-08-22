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
const ACC2_LAMPORTS: u64 = 4 * LAMPORTS_PER_SOL;
const DATA_LEN: usize = 16;
const ACC2_DATA_LEN: usize = 32;

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

fn layout_marker() -> u64 {
    let layout_sig = "1|0:dummy:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    let mut value: u64 = 0;
    for &b in &digest[..8] {
        value = (value << 8) | u64::from(b);
    }
    value
}

fn trio_state(initialized: bool) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    if initialized {
        data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    }
    data
}

fn instruction_data(disc_hex: &str, params: &[u64]) -> Vec<u8> {
    let mut data = discriminator_bytes(disc_hex).to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    data
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("PF_TRIO_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Trio.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Trio.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_account(program_id: &Pubkey) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, DATA_LEN, program_id);
    account.data = trio_state(true);
    account
}

fn peer_account(owner: &Pubkey, lamports: u64, data_len: usize) -> Account {
    Account::new(lamports, data_len, owner)
}

fn word0(key: &Pubkey) -> u64 {
    u64::from_le_bytes(key.to_bytes()[0..8].try_into().expect("8"))
}

fn build_ix(
    program_id: Pubkey,
    acc0: Pubkey,
    acc1: Pubkey,
    acc2: Option<Pubkey>,
    name: &str,
    signer1: bool,
    writable2: bool,
    signer2: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, 0);
    let mut metas = vec![
        AccountMeta::new_readonly(acc0, false),
        AccountMeta::new_readonly(acc1, signer1),
    ];
    if let Some(k) = acc2 {
        metas.push(if writable2 {
            AccountMeta::new(k, signer2)
        } else {
            AccountMeta::new_readonly(k, signer2)
        });
    }
    Instruction::new_with_bytes(program_id, &instruction_data(&disc, &[]), metas)
}

fn view(name: &str, expect: u64, signer1: bool, writable2: bool, signer2: bool) {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let acc2 = Pubkey::new_unique();
    let owner2 = Pubkey::new_unique();
    let ix = build_ix(
        program_id, acc0, acc1, Some(acc2), name, signer1, writable2, signer2,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id)),
            (acc1, peer_account(&Pubkey::new_unique(), BASE_LAMPORTS, 0)),
            (acc2, peer_account(&owner2, ACC2_LAMPORTS, ACC2_DATA_LEN)),
        ],
        &[
            Check::success(),
            Check::return_data(&expect.to_le_bytes()),
        ],
    );
}

#[test]
fn lamports2_returns_peer_balance() {
    view("lamports2", ACC2_LAMPORTS, false, false, false);
}

#[test]
fn data_len2_returns_32() {
    view("dataLen2", ACC2_DATA_LEN as u64, false, false, false);
}

#[test]
fn signer2_flag_tracks_meta() {
    view("signer2", 1, false, false, true);
    view("signer2", 0, false, false, false);
}

#[test]
fn writable2_flag_tracks_meta() {
    view("writable2", 1, false, true, false);
    view("writable2", 0, false, false, false);
}

#[test]
fn executable2_is_zero_for_data_account() {
    view("executable2", 0, false, false, false);
}

#[test]
fn key20_matches_acc2_pubkey() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let acc2 = Pubkey::new_unique();
    let ix = build_ix(
        program_id, acc0, acc1, Some(acc2), "key20", false, false, false,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id)),
            (acc1, peer_account(&Pubkey::new_unique(), BASE_LAMPORTS, 0)),
            (acc2, peer_account(&Pubkey::new_unique(), ACC2_LAMPORTS, ACC2_DATA_LEN)),
        ],
        &[
            Check::success(),
            Check::return_data(&word0(&acc2).to_le_bytes()),
        ],
    );
}

#[test]
fn need_sig1_rejects_missing_signer() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let acc2 = Pubkey::new_unique();
    let ix = build_ix(
        program_id, acc0, acc1, Some(acc2), "needSig1", false, false, false,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id)),
            (acc1, peer_account(&Pubkey::new_unique(), BASE_LAMPORTS, 0)),
            (acc2, peer_account(&Pubkey::new_unique(), ACC2_LAMPORTS, ACC2_DATA_LEN)),
        ],
        &[Check::err(ProgramError::Custom(1))],
    );
}

#[test]
fn need_sig1_returns_key_when_signed() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let acc2 = Pubkey::new_unique();
    let ix = build_ix(
        program_id, acc0, acc1, Some(acc2), "needSig1", true, false, false,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id)),
            (acc1, peer_account(&Pubkey::new_unique(), BASE_LAMPORTS, 0)),
            (acc2, peer_account(&Pubkey::new_unique(), ACC2_LAMPORTS, ACC2_DATA_LEN)),
        ],
        &[
            Check::success(),
            Check::return_data(&word0(&acc1).to_le_bytes()),
        ],
    );
}

#[test]
fn self0_is_zero_when_owned_by_program() {
    view("self0", 0, false, false, false);
}

#[test]
fn self2_is_one_when_owner_differs() {
    view("self2", 1, false, false, false);
}

#[test]
fn missing_third_account_fails() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let ix = build_ix(program_id, acc0, acc1, None, "lamports2", false, false, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id)),
            (acc1, peer_account(&Pubkey::new_unique(), BASE_LAMPORTS, 0)),
        ],
        &[Check::err(ProgramError::Custom(1))],
    );
}
