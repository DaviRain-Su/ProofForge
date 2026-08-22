use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const DATA_LEN: usize = 16;
const DEFAULT_SLOTS: u64 = 432_000;
const CUSTOM_SLOTS: u64 = 64_000;

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

fn epoch_state(initialized: bool, dummy: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    if initialized {
        data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    }
    data[8..16].copy_from_slice(&dummy.to_le_bytes());
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
) -> Instruction {
    let meta = if writable {
        AccountMeta::new(state_key, false)
    } else {
        AccountMeta::new_readonly(state_key, false)
    };
    Instruction::new_with_bytes(program_id, &instruction_data(disc_hex, params), vec![meta])
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("SOLANA_LEAN_EPOCH_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Epoch.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Epoch.so: {e}"));
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
fn span_returns_default_slots_per_epoch() {
    let (program_id, mollusk) = harness();
    assert_eq!(mollusk.sysvars.epoch_schedule.slots_per_epoch, DEFAULT_SLOTS);
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("span", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false);
    let pre = epoch_state(true, 7);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&DEFAULT_SLOTS.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn span_tracks_custom_slots_per_epoch() {
    let (program_id, mut mollusk) = harness();
    mollusk.sysvars.epoch_schedule.slots_per_epoch = CUSTOM_SLOTS;
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("span", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false);
    let pre = epoch_state(true, 0);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&CUSTOM_SLOTS.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn stamp_stores_slots_per_epoch() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("stamp", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, state_account(&program_id, epoch_state(true, 1)))],
        &[
            Check::success(),
            Check::return_data(&DEFAULT_SLOTS.to_le_bytes()),
            Check::account(&state_key)
                .data(&epoch_state(true, DEFAULT_SLOTS))
                .build(),
        ],
    );
}
