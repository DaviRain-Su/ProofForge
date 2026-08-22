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
const PEER_LAMPORTS: u64 = 3 * LAMPORTS_PER_SOL;
const DATA_LEN: usize = 16;
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

fn layout_marker() -> u64 {
    let layout_sig = "1|0:dummy:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    let mut value: u64 = 0;
    for &b in &digest[..8] {
        value = (value << 8) | u64::from(b);
    }
    value
}

fn keys_state(initialized: bool) -> Vec<u8> {
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
    PathBuf::from(env::var("PF_KEYS_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Keys.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Keys.so: {e}"));
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

fn peer_account(owner: &Pubkey) -> Account {
    Account::new(PEER_LAMPORTS, PEER_DATA_LEN, owner)
}

fn word_u64(bytes: &[u8; 32], word: usize) -> u64 {
    let off = word * 8;
    u64::from_le_bytes(bytes[off..off + 8].try_into().expect("8"))
}

fn build_ix(
    program_id: Pubkey,
    acc0: Pubkey,
    acc1: Option<Pubkey>,
    name: &str,
) -> Instruction {
    let disc = instruction_discriminator(name, 0);
    let mut metas = vec![AccountMeta::new_readonly(acc0, false)];
    if let Some(k) = acc1 {
        metas.push(AccountMeta::new_readonly(k, false));
    }
    Instruction::new_with_bytes(program_id, &instruction_data(&disc, &[]), metas)
}

fn view_word(name: &str, expected: u64) {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let ix = build_ix(program_id, acc0, Some(acc1), name);
    let pre = keys_state(true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id, pre.clone())),
            (acc1, peer_account(&owner1)),
        ],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
            Check::account(&acc0).data(&pre).build(),
        ],
    );
}

#[test]
fn initialize_walk_succeeds_with_two_accounts() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let disc = instruction_discriminator("initialize", 1);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[9]),
        vec![
            AccountMeta::new(acc0, true),
            AccountMeta::new_readonly(acc1, false),
        ],
    );
    // walk 程序的 init 只过账户数检查，不写 layout marker。
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id, keys_state(false))),
            (acc1, peer_account(&owner1)),
        ],
        &[Check::success()],
    );
}

#[test]
fn key0_words_match_pubkey() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let bytes = acc0.to_bytes();
    let pre = keys_state(true);
    for (name, word) in [("key00", 0), ("key01", 1), ("key02", 2), ("key03", 3)] {
        let ix = build_ix(program_id, acc0, Some(acc1), name);
        mollusk.process_and_validate_instruction(
            &ix,
            &[
                (acc0, state_account(&program_id, pre.clone())),
                (acc1, peer_account(&owner1)),
            ],
            &[
                Check::success(),
                Check::return_data(&word_u64(&bytes, word).to_le_bytes()),
                Check::account(&acc0).data(&pre).build(),
            ],
        );
    }
}

#[test]
fn owner0_words_match_program_id() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let bytes = program_id.to_bytes();
    let pre = keys_state(true);
    for (name, word) in [("owner00", 0), ("owner03", 3)] {
        let ix = build_ix(program_id, acc0, Some(acc1), name);
        mollusk.process_and_validate_instruction(
            &ix,
            &[
                (acc0, state_account(&program_id, pre.clone())),
                (acc1, peer_account(&owner1)),
            ],
            &[
                Check::success(),
                Check::return_data(&word_u64(&bytes, word).to_le_bytes()),
            ],
        );
    }
}

#[test]
fn key1_words_match_pubkey() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let bytes = acc1.to_bytes();
    let pre = keys_state(true);
    for (name, word) in [("key10", 0), ("key13", 3)] {
        let ix = build_ix(program_id, acc0, Some(acc1), name);
        mollusk.process_and_validate_instruction(
            &ix,
            &[
                (acc0, state_account(&program_id, pre.clone())),
                (acc1, peer_account(&owner1)),
            ],
            &[
                Check::success(),
                Check::return_data(&word_u64(&bytes, word).to_le_bytes()),
            ],
        );
    }
}

#[test]
fn owner1_words_match_owner() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let bytes = owner1.to_bytes();
    let pre = keys_state(true);
    for (name, word) in [("owner10", 0), ("owner13", 3)] {
        let ix = build_ix(program_id, acc0, Some(acc1), name);
        mollusk.process_and_validate_instruction(
            &ix,
            &[
                (acc0, state_account(&program_id, pre.clone())),
                (acc1, peer_account(&owner1)),
            ],
            &[
                Check::success(),
                Check::return_data(&word_u64(&bytes, word).to_le_bytes()),
            ],
        );
    }
}

#[test]
fn key00_does_not_require_signer() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let acc1 = Pubkey::new_unique();
    let owner1 = Pubkey::new_unique();
    let expected = word_u64(&acc0.to_bytes(), 0);
    let ix = build_ix(program_id, acc0, Some(acc1), "key00");
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (acc0, state_account(&program_id, keys_state(true))),
            (acc1, peer_account(&owner1)),
        ],
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
        ],
    );
}

#[test]
fn missing_second_account_fails_on_acc1_word() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let ix = build_ix(program_id, acc0, None, "key10");
    mollusk.process_and_validate_instruction(
        &ix,
        &[(acc0, state_account(&program_id, keys_state(true)))],
        &[Check::err(ProgramError::Custom(1))],
    );
}

#[test]
fn key00_is_stable() {
    view_word("get", 0);
}
