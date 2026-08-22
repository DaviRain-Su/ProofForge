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

fn hash_state(initialized: bool) -> Vec<u8> {
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
    PathBuf::from(env::var("PF_HASH_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Hash.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Hash.so: {e}"));
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

fn host_first_u64(seed: &[u8]) -> u64 {
    let digest = Sha256::digest(seed);
    u64::from_le_bytes(digest[..8].try_into().expect("8"))
}

fn assert_hash_view(ix_name: &str, seed: &[u8]) {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator(ix_name, 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = hash_state(true);
    let account = state_account(&program_id, pre.clone());
    let expected = host_first_u64(seed);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn initialize_clears_dummy() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("initialize", 1);
    let ix = build_ix(program_id, state_key, &disc, &[9], true, true);
    let account = state_account(&program_id, hash_state(false));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::account(&state_key).data(&hash_state(true)).build(),
        ],
    );
}

#[test]
fn vault_matches_host_sha256() {
    assert_hash_view("vault", b"vault");
}

#[test]
fn ok_matches_host_sha256() {
    assert_hash_view("ok", b"ok");
}

#[test]
fn empty_matches_host_sha256() {
    assert_hash_view("empty", b"");
}

#[test]
fn vault_is_stable_across_two_calls() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("vault", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = hash_state(true);
    let expected = host_first_u64(b"vault");
    let first = mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, state_account(&program_id, pre.clone()))],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
        ],
    );
    let after = first
        .resulting_accounts
        .into_iter()
        .find(|(k, _)| k == &state_key)
        .expect("state")
        .1;
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, after)],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}
