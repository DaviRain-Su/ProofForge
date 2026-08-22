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
    let layout_sig = "2|0:open_:0:8:1:u8-le|1:dummy:0:9:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    let mut value: u64 = 0;
    for &b in &digest[..8] {
        value = (value << 8) | u64::from(b);
    }
    value
}

fn gate_state(initialized: bool, open: u8) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    if initialized {
        data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    }
    data[8] = open;
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
    name: &str,
    param_count: usize,
    params: &[u64],
    writable: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, param_count);
    let meta = if writable {
        AccountMeta::new(state_key, true)
    } else {
        AccountMeta::new_readonly(state_key, false)
    };
    Instruction::new_with_bytes(program_id, &instruction_data(&disc, params), vec![meta])
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("PF_GATE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Gate.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Gate.so: {e}"));
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
fn initialize_clears_bool() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let ix = build_ix(program_id, state_key, "initialize", 1, &[9], true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, state_account(&program_id, gate_state(false, 1)))],
        &[
            Check::success(),
            Check::account(&state_key)
                .data(&gate_state(true, 0))
                .build(),
        ],
    );
}

#[test]
fn open_writes_true_then_is_open() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let open_ix = build_ix(program_id, state_key, "openGate", 0, &[], true);
    let result = mollusk.process_and_validate_instruction(
        &open_ix,
        &[(state_key, state_account(&program_id, gate_state(true, 0)))],
        &[
            Check::success(),
            Check::return_data(&1u64.to_le_bytes()),
            Check::account(&state_key)
                .data(&gate_state(true, 1))
                .build(),
        ],
    );
    let after = result
        .resulting_accounts
        .into_iter()
        .find(|(k, _)| k == &state_key)
        .expect("state")
        .1;
    let view = build_ix(program_id, state_key, "isOpen", 0, &[], false);
    mollusk.process_and_validate_instruction(
        &view,
        &[(state_key, after)],
        &[
            Check::success(),
            Check::return_data(&1u64.to_le_bytes()),
        ],
    );
}

#[test]
fn now_tracks_warped_unix() {
    let (program_id, mut mollusk) = harness();
    mollusk.sysvars.clock.unix_timestamp = 1_700_000_123;
    let unix = mollusk.sysvars.clock.unix_timestamp as u64;
    let state_key = Pubkey::new_unique();
    let ix = build_ix(program_id, state_key, "now", 0, &[], false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, state_account(&program_id, gate_state(true, 0)))],
        &[
            Check::success(),
            Check::return_data(&unix.to_le_bytes()),
        ],
    );
}
