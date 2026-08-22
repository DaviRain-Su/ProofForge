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
const ARITHMETIC_OVERFLOW: u32 = 0x1001;
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const DATA_LEN: usize = 24;

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
    let layout_sig = "2|0:left:0:8:8:u64-le|1:right:0:16:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    let mut value: u64 = 0;
    for &b in &digest[..8] {
        value = (value << 8) | u64::from(b);
    }
    value
}

fn pair_state(initialized: bool, left: u64, right: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    if initialized {
        data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    }
    data[8..16].copy_from_slice(&left.to_le_bytes());
    data[16..24].copy_from_slice(&right.to_le_bytes());
    data
}

fn instruction_data(disc_hex: &str, params: &[u64]) -> Vec<u8> {
    let mut data = discriminator_bytes(disc_hex).to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    data
}

fn build_ix(
    program_id: Pubkey,
    state_key: Pubkey,
    disc_hex: &str,
    params: &[u64],
    writable: bool,
    signer: bool,
) -> Instruction {
    let meta = if writable {
        AccountMeta::new(state_key, signer)
    } else {
        AccountMeta::new_readonly(state_key, signer)
    };
    Instruction::new_with_bytes(program_id, &instruction_data(disc_hex, params), vec![meta])
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("SOLANA_LEAN_PAIR_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Pair.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Pair.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn state_account(program_id: &Pubkey, data: Vec<u8>) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, data.len(), program_id);
    account.data = data;
    account
}

#[test]
fn initialize_sets_left_and_zero_right() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("initialize", 1);
    let ix = build_ix(program_id, state_key, &disc, &[7], true, true);
    let account = state_account(&program_id, pair_state(false, 0, 0));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::account(&state_key)
                .data(&pair_state(true, 7, 0))
                .build(),
        ],
    );
}

#[test]
fn credit_left_keeps_right() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("creditLeft", 1);
    let ix = build_ix(program_id, state_key, &disc, &[3], true, false);
    let account = state_account(&program_id, pair_state(true, 5, 99));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&8u64.to_le_bytes()),
            Check::account(&state_key)
                .data(&pair_state(true, 8, 99))
                .build(),
        ],
    );
}

#[test]
fn get_returns_left() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("getLeft", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let account = state_account(&program_id, pair_state(true, 8, 99));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&8u64.to_le_bytes()),
            Check::account(&state_key)
                .data(&pair_state(true, 8, 99))
                .build(),
        ],
    );
}

#[test]
fn init_both_writes_left_and_right() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("initBoth", 2);
    let ix = build_ix(program_id, state_key, &disc, &[3, 9], true, true);
    let account = state_account(&program_id, pair_state(false, 0, 0));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::account(&state_key)
                .data(&pair_state(true, 3, 9))
                .build(),
        ],
    );
}

#[test]
fn get_returns_right() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("getRight", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let account = state_account(&program_id, pair_state(true, 8, 99));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&99u64.to_le_bytes()),
            Check::account(&state_key)
                .data(&pair_state(true, 8, 99))
                .build(),
        ],
    );
}

#[test]
fn credit_left_overflow_holds() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("creditLeft", 1);
    let pre = pair_state(true, u64::MAX, 99);
    let ix = build_ix(program_id, state_key, &disc, &[1], true, false);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::err(ProgramError::Custom(ARITHMETIC_OVERFLOW)),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}
