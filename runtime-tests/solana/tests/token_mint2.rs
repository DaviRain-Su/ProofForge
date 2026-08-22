use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;
const MINT_LEN: usize = 82;

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
    PathBuf::from(env::var("PF_TOKENMINT2_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenMint2.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenMint2.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn uninitialized_mint() -> Account {
    Account::new(
        Rent::default().minimum_balance(MINT_LEN),
        MINT_LEN,
        &token::ID,
    )
}

fn build_ix(
    program_id: Pubkey,
    authority: Pubkey,
    mint: Pubkey,
    token_id: Pubkey,
    authority_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("openMint", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(authority, authority_signer),
            AccountMeta::new(mint, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn init_mint_writes_authority_and_decimals() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, authority, mint, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (authority, funded(LAMPORTS_PER_SOL)),
            (mint, uninitialized_mint()),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&mint)
                .owner(&token::ID)
                .space(MINT_LEN)
                .data_slice(36 + 8, &[DECIMALS])
                .data_slice(36 + 8 + 1, &[1])
                .build(),
        ],
    );
}

#[test]
fn init_mint_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, authority, mint, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (authority, funded(LAMPORTS_PER_SOL)),
            (mint, uninitialized_mint()),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&mint).data_slice(36 + 8 + 1, &[0]).build(),
        ],
    );
}
