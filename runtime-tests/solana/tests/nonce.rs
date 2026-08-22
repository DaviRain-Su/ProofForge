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
const NONCE_LEN: usize = 80;

fn system_id() -> Pubkey {
    Pubkey::new_from_array([0u8; 32])
}

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
    PathBuf::from(env::var("SOLANA_LEAN_NONCE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Nonce.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Nonce.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn funded() -> Account {
    Account::new(LAMPORTS_PER_SOL, 0, &Pubkey::default())
}

fn build_ix(
    program_id: Pubkey,
    authority: Pubkey,
    nonce: Pubkey,
    recent: Pubkey,
    authority_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("advance", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(authority, authority_signer),
            AccountMeta::new(nonce, false),
            AccountMeta::new_readonly(recent, false),
            AccountMeta::new_readonly(system_id(), false),
        ],
    )
}

#[test]
fn advance_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let nonce = Pubkey::new_unique();
    let recent = Pubkey::new_unique();
    let ix = build_ix(program_id, authority, nonce, recent, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (authority, funded()),
            (nonce, Account::new(LAMPORTS_PER_SOL, NONCE_LEN, &system_id())),
            (recent, funded()),
            (system_id(), Account::new(1, 0, &system_id())),
        ],
        &[Check::err(ProgramError::Custom(1))],
    );
}
