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
    let layout_sig = "1|0:stamped:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout_sig}").as_bytes());
    let mut value: u64 = 0;
    for &b in &digest[..8] {
        value = (value << 8) | u64::from(b);
    }
    value
}

fn clock_state(initialized: bool, stamped: u64) -> Vec<u8> {
    let mut data = vec![0u8; DATA_LEN];
    if initialized {
        data[..8].copy_from_slice(&layout_marker().to_le_bytes());
    }
    data[8..16].copy_from_slice(&stamped.to_le_bytes());
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
    PathBuf::from(env::var("PF_CLOCK_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Clock.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Clock.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn warped(slot: u64) -> (Pubkey, Mollusk) {
    let (program_id, mut mollusk) = harness();
    mollusk.sysvars.warp_to_slot(slot);
    assert_eq!(
        mollusk.sysvars.clock.slot, slot,
        "warp_to_slot must set Clock.slot"
    );
    (program_id, mollusk)
}

fn warped_epoch(slot: u64) -> (Pubkey, Mollusk, u64) {
    let (program_id, mollusk) = warped(slot);
    let epoch = mollusk.sysvars.clock.epoch;
    (program_id, mollusk, epoch)
}

fn state_account(program_id: &Pubkey, data: Vec<u8>) -> Account {
    let mut account = Account::new(BASE_LAMPORTS, data.len(), program_id);
    account.data = data;
    account
}

fn key0_u64(key: &Pubkey) -> u64 {
    let bytes = key.to_bytes();
    u64::from_le_bytes(bytes[0..8].try_into().expect("8"))
}

#[test]
fn initialize_clears_stamped() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("initialize", 1);
    let ix = build_ix(program_id, state_key, &disc, &[9], true, true);
    let account = state_account(&program_id, clock_state(false, 9));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::account(&state_key)
                .data(&clock_state(true, 0))
                .build(),
        ],
    );
}

#[test]
fn height_returns_warped_slot() {
    let slot = 4242u64;
    let (program_id, mollusk) = warped(slot);
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("height", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = clock_state(true, 7);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&slot.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn height_tracks_second_distinct_slot() {
    let slot = 987_654_321u64;
    let (program_id, mollusk) = warped(slot);
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("height", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = clock_state(true, 0);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&slot.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn era_returns_warped_epoch() {
    let slot = 0u64;
    let (program_id, mollusk, epoch) = warped_epoch(slot);
    assert_eq!(epoch, 0, "slot 0 is epoch 0");
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("era", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = clock_state(true, 7);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&epoch.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn era_tracks_second_distinct_epoch() {
    let slot = 800_000u64;
    let (program_id, mollusk, epoch) = warped_epoch(slot);
    assert_ne!(epoch, 0, "slot 800_000 must leave epoch 0");
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("era", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let pre = clock_state(true, 0);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&epoch.to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn stamp_stores_current_slot_then_get_reads_it() {
    let slot = 123_456u64;
    let (program_id, mollusk) = warped(slot);
    let state_key = Pubkey::new_unique();

    let stamp_disc = instruction_discriminator("stamp", 0);
    let stamp_ix = build_ix(program_id, state_key, &stamp_disc, &[], true, false);
    let result = mollusk.process_and_validate_instruction(
        &stamp_ix,
        &[(state_key, state_account(&program_id, clock_state(true, 1)))],
        &[
            Check::success(),
            Check::return_data(&slot.to_le_bytes()),
            Check::account(&state_key)
                .data(&clock_state(true, slot))
                .build(),
        ],
    );
    let after_stamp = result
        .resulting_accounts
        .into_iter()
        .find(|(k, _)| k == &state_key)
        .expect("state account after stamp")
        .1;

    let get_disc = instruction_discriminator("get", 0);
    let get_ix = build_ix(program_id, state_key, &get_disc, &[], false, false);
    mollusk.process_and_validate_instruction(
        &get_ix,
        &[(state_key, after_stamp)],
        &[
            Check::success(),
            Check::return_data(&slot.to_le_bytes()),
            Check::account(&state_key)
                .data(&clock_state(true, slot))
                .build(),
        ],
    );
}

#[test]
fn key0_returns_first_u64_when_signer() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("key0", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, true);
    let pre = clock_state(true, 0);
    let account = state_account(&program_id, pre.clone());
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[
            Check::success(),
            Check::return_data(&key0_u64(&state_key).to_le_bytes()),
            Check::account(&state_key).data(&pre).build(),
        ],
    );
}

#[test]
fn key0_rejects_missing_signer() {
    let (program_id, mollusk) = harness();
    let state_key = Pubkey::new_unique();
    let disc = instruction_discriminator("key0", 0);
    let ix = build_ix(program_id, state_key, &disc, &[], false, false);
    let account = state_account(&program_id, clock_state(true, 0));
    mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, account)],
        &[Check::err(ProgramError::Custom(1))],
    );
}
