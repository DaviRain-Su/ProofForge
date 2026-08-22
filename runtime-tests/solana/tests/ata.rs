use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::{associated_token, token},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    spl_associated_token_account_interface::address::get_associated_token_address_with_program_id,
    spl_token_interface::state::{Account as TokenAccount, AccountState, Mint},
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;

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
    PathBuf::from(env::var("SOLANA_LEAN_ATA_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Ata.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Ata.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    associated_token::add_program(&mut mollusk);
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

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn empty_system() -> Account {
    Account::new(0, 0, &Pubkey::default())
}

fn build_ix(
    program_id: Pubkey,
    payer: Pubkey,
    ata: Pubkey,
    wallet: Pubkey,
    mint: Pubkey,
    system: Pubkey,
    token_id: Pubkey,
    ata_prog: Pubkey,
    payer_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("openAta", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(payer, payer_signer),
            AccountMeta::new(ata, false),
            AccountMeta::new_readonly(wallet, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(system, false),
            AccountMeta::new_readonly(token_id, false),
            AccountMeta::new_readonly(ata_prog, false),
        ],
    )
}

#[test]
fn ata_creates_token_account_for_wallet() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let wallet = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let ata = get_associated_token_address_with_program_id(&wallet, &mint, &token::ID);
    let (system, system_acc) = mollusk_svm::program::keyed_account_for_system_program();
    let (token_id, token_acc) = token::keyed_account();
    let (ata_prog, ata_prog_acc) = associated_token::keyed_account();
    let ix = build_ix(
        program_id, payer, ata, wallet, mint, system, token_id, ata_prog, true,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(10 * LAMPORTS_PER_SOL)),
            (ata, empty_system()),
            (wallet, funded(LAMPORTS_PER_SOL)),
            (mint, mint_account(wallet)),
            (system, system_acc),
            (token_id, token_acc),
            (ata_prog, ata_prog_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&ata)
                .owner(&token::ID)
                .space(165)
                .build(),
        ],
    );
}

#[test]
fn ata_idempotent_when_already_exists() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let wallet = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (ata, ata_acc) = associated_token::create_account_for_associated_token_account(TokenAccount {
        mint,
        owner: wallet,
        amount: 0,
        delegate: None.into(),
        state: AccountState::Initialized,
        is_native: None.into(),
        delegated_amount: 0,
        close_authority: None.into(),
    });
    let (system, system_acc) = mollusk_svm::program::keyed_account_for_system_program();
    let (token_id, token_acc) = token::keyed_account();
    let (ata_prog, ata_prog_acc) = associated_token::keyed_account();
    let ix = build_ix(
        program_id, payer, ata, wallet, mint, system, token_id, ata_prog, true,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(10 * LAMPORTS_PER_SOL)),
            (ata, ata_acc),
            (wallet, funded(LAMPORTS_PER_SOL)),
            (mint, mint_account(wallet)),
            (system, system_acc),
            (token_id, token_acc),
            (ata_prog, ata_prog_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&ata).owner(&token::ID).space(165).build(),
        ],
    );
}

#[test]
fn ata_missing_payer_signer_fails() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let wallet = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let ata = get_associated_token_address_with_program_id(&wallet, &mint, &token::ID);
    let (system, system_acc) = mollusk_svm::program::keyed_account_for_system_program();
    let (token_id, token_acc) = token::keyed_account();
    let (ata_prog, ata_prog_acc) = associated_token::keyed_account();
    let ix = build_ix(
        program_id, payer, ata, wallet, mint, system, token_id, ata_prog, false,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(10 * LAMPORTS_PER_SOL)),
            (ata, empty_system()),
            (wallet, funded(LAMPORTS_PER_SOL)),
            (mint, mint_account(wallet)),
            (system, system_acc),
            (token_id, token_acc),
            (ata_prog, ata_prog_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&ata).lamports(0).build(),
        ],
    );
}
