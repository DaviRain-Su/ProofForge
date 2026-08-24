mod common;

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
const ALLOW: u64 = 1_000_000;

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
    PathBuf::from(env::var("PF_TOKENAPPROVE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenApprove.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenApprove.so: {e}"));
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
        supply: INITIAL,
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
    owner: Pubkey,
    source: Pubkey,
    mint: Pubkey,
    delegate: Pubkey,
    token_id: Pubkey,
    owner_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("approve", 1);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[ALLOW]),
        vec![
            AccountMeta::new(common::dummy_state_key(&program_id), false),
            AccountMeta::new(owner, owner_signer),
            AccountMeta::new(source, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(delegate, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn approve_writes_delegate_and_amount() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let delegate = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, owner, source, mint, delegate, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (owner, funded()),
            (source, token_account(mint, owner, INITIAL)),
            (mint, mint_account(owner)),
            (delegate, funded()),
            (token_id, token_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&ALLOW.to_le_bytes()),
            Check::account(&source)
                .data_slice(72, &[1, 0, 0, 0])
                .data_slice(76, delegate.as_ref())
                .data_slice(121, &ALLOW.to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn approve_missing_owner_signer_fails() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let delegate = Pubkey::new_unique();
    let (token_id, token_acc) = token::keyed_account();
    let ix = build_ix(program_id, owner, source, mint, delegate, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (owner, funded()),
            (source, token_account(mint, owner, INITIAL)),
            (mint, mint_account(owner)),
            (delegate, funded()),
            (token_id, token_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&source)
                .data_slice(72, &[0, 0, 0, 0])
                .data_slice(121, &0u64.to_le_bytes())
                .build(),
        ],
    );
}
