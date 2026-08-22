use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const MULTISIG_LEN: usize = 355;

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
    PathBuf::from(env::var("PF_TOKENMS_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenMs.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenMs.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn funded() -> Account {
    Account::new(LAMPORTS_PER_SOL, 0, &Pubkey::default())
}

fn empty_multisig(token_id: &Pubkey) -> Account {
    Account::new(LAMPORTS_PER_SOL, MULTISIG_LEN, token_id)
}

fn build_ix(
    program_id: Pubkey,
    payer: Pubkey,
    ms: Pubkey,
    s0: Pubkey,
    s1: Pubkey,
    token_id: Pubkey,
    payer_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("openMs", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(payer, payer_signer),
            AccountMeta::new(ms, false),
            AccountMeta::new_readonly(s0, false),
            AccountMeta::new_readonly(s1, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn init_multisig_sets_m_and_n() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let ms = Pubkey::new_unique();
    let s0 = Pubkey::new_unique();
    let s1 = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, payer, ms, s0, s1, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded()),
            (ms, empty_multisig(&token_id)),
            (s0, funded()),
            (s1, funded()),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&ms)
                .data_slice(0, &[2])
                .data_slice(1, &[2])
                .build(),
        ],
    );
}

#[test]
fn init_multisig_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let ms = Pubkey::new_unique();
    let s0 = Pubkey::new_unique();
    let s1 = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, payer, ms, s0, s1, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded()),
            (ms, empty_multisig(&token_id)),
            (s0, funded()),
            (s1, funded()),
            (token_id, token_acc),
        ],
        &[Check::err(ProgramError::Custom(1))],
    );
}
