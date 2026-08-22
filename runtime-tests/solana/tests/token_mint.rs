use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    spl_token_interface::state::{Account as TokenAccount, AccountState, Mint},
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;
const INITIAL: u64 = 10_000_000;
const DELTA: u64 = 1_000_000;

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
    PathBuf::from(env::var("PF_TOKENMINT_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenMint.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenMint.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn mint_account(authority: Pubkey, supply: u64) -> Account {
    token::create_account_for_mint(Mint {
        mint_authority: Some(authority).into(),
        supply,
        decimals: DECIMALS,
        is_initialized: true,
        freeze_authority: None.into(),
    })
}

fn token_account(mint: Pubkey, owner: Pubkey, amount: u64) -> Account {
    token::create_account_for_token_account(TokenAccount {
        mint,
        owner,
        amount,
        delegate: None.into(),
        state: AccountState::Initialized,
        is_native: None.into(),
        delegated_amount: 0,
        close_authority: None.into(),
    })
}

fn funded() -> Account {
    Account::new(LAMPORTS_PER_SOL, 0, &Pubkey::default())
}

fn build_ix(
    program_id: Pubkey,
    name: &str,
    authority: Pubkey,
    acc1: Pubkey,
    acc2: Pubkey,
    token_id: Pubkey,
    authority_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, 1);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[DELTA]),
        vec![
            AccountMeta::new(authority, authority_signer),
            AccountMeta::new(acc1, false),
            AccountMeta::new(acc2, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn mint_to_increases_dest_and_supply() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let dest = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "mintTo", authority, mint, dest, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (authority, funded()),
            (mint, mint_account(authority, INITIAL)),
            (dest, token_account(mint, authority, 0)),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&DELTA.to_le_bytes()),
            Check::account(&dest)
                .data_slice(64, &DELTA.to_le_bytes())
                .build(),
            Check::account(&mint)
                .data_slice(36, &(INITIAL + DELTA).to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn mint_missing_authority_signer_fails() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let dest = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "mintTo", authority, mint, dest, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (authority, funded()),
            (mint, mint_account(authority, INITIAL)),
            (dest, token_account(mint, authority, 0)),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&dest).data_slice(64, &0u64.to_le_bytes()).build(),
        ],
    );
}

#[test]
fn burn_decreases_source_and_supply() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "burn", owner, source, mint, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded()),
            (source, token_account(mint, owner, INITIAL)),
            (mint, mint_account(owner, INITIAL)),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&DELTA.to_le_bytes()),
            Check::account(&source)
                .data_slice(64, &(INITIAL - DELTA).to_le_bytes())
                .build(),
            Check::account(&mint)
                .data_slice(36, &(INITIAL - DELTA).to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn burn_missing_owner_signer_fails() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "burn", owner, source, mint, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded()),
            (source, token_account(mint, owner, INITIAL)),
            (mint, mint_account(owner, INITIAL)),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&source)
                .data_slice(64, &INITIAL.to_le_bytes())
                .build(),
        ],
    );
}
