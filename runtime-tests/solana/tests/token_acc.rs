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
    spl_token_interface::state::{Account as TokenAccount, AccountState, Mint},
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;
const TOKEN_ACCOUNT_LEN: usize = 165;

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
    PathBuf::from(env::var("PF_TOKENACC_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenAcc.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenAcc.so: {e}"));
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

fn uninitialized_token_account() -> Account {
    Account::new(
        Rent::default().minimum_balance(TOKEN_ACCOUNT_LEN),
        TOKEN_ACCOUNT_LEN,
        &token::ID,
    )
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn build_ix(
    program_id: Pubkey,
    name: &str,
    owner: Pubkey,
    acc1: Pubkey,
    acc2: Pubkey,
    token_id: Pubkey,
    owner_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(owner, owner_signer),
            AccountMeta::new(acc1, false),
            AccountMeta::new(acc2, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn init_writes_owner_and_mint() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let account = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "openAcc", owner, account, mint, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded(LAMPORTS_PER_SOL)),
            (account, uninitialized_token_account()),
            (mint, mint_account(owner)),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&account)
                .owner(&token::ID)
                .space(TOKEN_ACCOUNT_LEN)
                .data_slice(0, mint.as_ref())
                .data_slice(32, owner.as_ref())
                .build(),
        ],
    );
}

#[test]
fn init_missing_owner_signer_fails() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let account = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, "openAcc", owner, account, mint, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded(LAMPORTS_PER_SOL)),
            (account, uninitialized_token_account()),
            (mint, mint_account(owner)),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&account)
                .data_slice(0, &[0u8; 32])
                .build(),
        ],
    );
}

#[test]
fn close_returns_lamports_to_dest() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let dest = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let source_acc = token_account(mint, owner, 0);
    let source_lamports = source_acc.lamports;
    let dest_before = LAMPORTS_PER_SOL;
    let ix = build_ix(program_id, "closeAcc", owner, source, dest, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded(LAMPORTS_PER_SOL)),
            (source, source_acc),
            (dest, funded(dest_before)),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&source).lamports(0).build(),
            Check::account(&dest)
                .lamports(dest_before + source_lamports)
                .build(),
        ],
    );
}

#[test]
fn close_missing_owner_signer_fails() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let dest = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let source_acc = token_account(mint, owner, 0);
    let source_lamports = source_acc.lamports;
    let ix = build_ix(program_id, "closeAcc", owner, source, dest, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (owner, funded(LAMPORTS_PER_SOL)),
            (source, source_acc),
            (dest, funded(LAMPORTS_PER_SOL)),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&source).lamports(source_lamports).build(),
        ],
    );
}
