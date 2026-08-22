use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    spl_token_interface::state::Mint,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;
const TOKEN_ACCOUNT_LEN: u64 = 165;

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
    PathBuf::from(env::var("SOLANA_LEAN_TOKENSIZE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenSize.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenSize.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn mint_account(authority: Pubkey) -> Account {
    token::create_account_for_mint(Mint {
        mint_authority: Some(authority).into(),
        supply: 0,
        decimals: DECIMALS,
        is_initialized: true,
        freeze_authority: None.into(),
    })
}

fn funded() -> Account {
    Account::new(LAMPORTS_PER_SOL, 0, &Pubkey::default())
}

fn build_ix(
    program_id: Pubkey,
    dummy: Pubkey,
    mint: Pubkey,
    token_id: Pubkey,
    dummy_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("size", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(dummy, dummy_signer),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn size_returns_classic_token_account_len() {
    let (program_id, mollusk) = harness();
    let dummy = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, dummy, mint, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (dummy, funded()),
            (mint, mint_account(dummy)),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&TOKEN_ACCOUNT_LEN.to_le_bytes()),
        ],
    );
}

#[test]
fn size_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let dummy = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, dummy, mint, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (dummy, funded()),
            (mint, mint_account(dummy)),
            (token_id, token_acc),
        ],
        &[Check::err(ProgramError::Custom(1))],
    );
}
