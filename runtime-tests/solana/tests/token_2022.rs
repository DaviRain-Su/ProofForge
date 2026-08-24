mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token2022,
    mollusk_svm_programs_token_2022::{
        create_account_for_mint_with_extensions, Mint as Token2022Mint, MintExtension,
        TransferFeeConfig, TransferHook,
    },
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    spl_token_2022_interface::extension::transfer_fee::TransferFee,
    spl_token_interface::state::{Account as TokenAccount, AccountState, Mint},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const DECIMALS: u8 = 6;
const INITIAL: u64 = 10_000_000;
const SEND: u64 = 1_000_000;

fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    let digest = Sha256::digest(preimage.as_bytes());
    digest[..8].try_into().unwrap()
}

fn instruction_data(params: &[u64]) -> Vec<u8> {
    let mut data = instruction_discriminator("send", 1).to_vec();
    for param in params {
        data.extend_from_slice(&param.to_le_bytes());
    }
    data
}

fn harness() -> (Pubkey, Mollusk) {
    let (program_id, mut mollusk) = common::harness("Token2022", "PF_TOKEN_2022_SO");
    token2022::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn mint_data(authority: Pubkey) -> Mint {
    Mint {
        mint_authority: Some(authority).into(),
        supply: INITIAL,
        decimals: DECIMALS,
        is_initialized: true,
        freeze_authority: None.into(),
    }
}

fn base_mint_account(authority: Pubkey) -> Account {
    token2022::create_account_for_mint(mint_data(authority))
}

fn extension_mint_data(authority: Pubkey) -> Token2022Mint {
    Token2022Mint {
        mint_authority: Some(authority).into(),
        supply: INITIAL,
        decimals: DECIMALS,
        is_initialized: true,
        freeze_authority: None.into(),
    }
}

fn base_token_account(mint: Pubkey, owner: Pubkey, amount: u64) -> Account {
    token2022::create_account_for_token_account(TokenAccount {
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
    authority: Pubkey,
    source: Pubkey,
    mint: Pubkey,
    destination: Pubkey,
    authority_signer: bool,
) -> Instruction {
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&[SEND]),
        vec![
            AccountMeta::new(common::dummy_state_key(&program_id), false),
            AccountMeta::new(authority, authority_signer),
            AccountMeta::new(source, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(destination, false),
            AccountMeta::new_readonly(token2022::ID, false),
        ],
    )
}

#[test]
fn token_2022_base_transfer_checked_moves_exact_amount() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let destination = Pubkey::new_unique();
    let ix = build_ix(program_id, authority, source, mint, destination, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (
                common::dummy_state_key(&program_id),
                common::dummy_state_account(&program_id),
            ),
            (authority, funded()),
            (source, base_token_account(mint, authority, INITIAL)),
            (mint, base_mint_account(authority)),
            (
                destination,
                base_token_account(mint, Pubkey::new_unique(), 0),
            ),
            token2022::keyed_account(),
        ],
        &[
            Check::success(),
            Check::return_data(&SEND.to_le_bytes()),
            Check::account(&source)
                .data_slice(64, &(INITIAL - SEND).to_le_bytes())
                .build(),
            Check::account(&destination)
                .data_slice(64, &SEND.to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn token_2022_missing_authority_signer_fails() {
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let destination = Pubkey::new_unique();
    let ix = build_ix(program_id, authority, source, mint, destination, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (
                common::dummy_state_key(&program_id),
                common::dummy_state_account(&program_id),
            ),
            (authority, funded()),
            (source, base_token_account(mint, authority, INITIAL)),
            (mint, base_mint_account(authority)),
            (
                destination,
                base_token_account(mint, Pubkey::new_unique(), 0),
            ),
            token2022::keyed_account(),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&source)
                .data_slice(64, &INITIAL.to_le_bytes())
                .build(),
            Check::account(&destination)
                .data_slice(64, &0u64.to_le_bytes())
                .build(),
        ],
    );
}

fn transfer_fee_mint(authority: Pubkey) -> Account {
    let fee = TransferFee {
        epoch: 0.into(),
        maximum_fee: 5_000.into(),
        transfer_fee_basis_points: 100.into(),
    };
    create_account_for_mint_with_extensions(
        extension_mint_data(authority),
        &[MintExtension::TransferFeeConfig(TransferFeeConfig {
            transfer_fee_config_authority: Some(authority).try_into().unwrap(),
            withdraw_withheld_authority: Some(authority).try_into().unwrap(),
            withheld_amount: 0.into(),
            older_transfer_fee: fee,
            newer_transfer_fee: fee,
        })],
    )
}

fn transfer_hook_mint(authority: Pubkey) -> Account {
    create_account_for_mint_with_extensions(
        extension_mint_data(authority),
        &[MintExtension::TransferHook(TransferHook {
            authority: Some(authority).try_into().unwrap(),
            program_id: Some(Pubkey::new_unique()).try_into().unwrap(),
        })],
    )
}

fn assert_extension_mint_rejected(mint_account: Account) {
    assert!(mint_account.data.len() > 82);
    let (program_id, mollusk) = harness();
    let authority = Pubkey::new_unique();
    let source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let destination = Pubkey::new_unique();
    let ix = build_ix(program_id, authority, source, mint, destination, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (
                common::dummy_state_key(&program_id),
                common::dummy_state_account(&program_id),
            ),
            (authority, funded()),
            (source, base_token_account(mint, authority, INITIAL)),
            (mint, mint_account),
            (
                destination,
                base_token_account(mint, Pubkey::new_unique(), 0),
            ),
            token2022::keyed_account(),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&source)
                .data_slice(64, &INITIAL.to_le_bytes())
                .build(),
            Check::account(&destination)
                .data_slice(64, &0u64.to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn token_2022_transfer_fee_mint_fails_closed() {
    let authority = Pubkey::new_unique();
    assert_extension_mint_rejected(transfer_fee_mint(authority));
}

#[test]
fn token_2022_transfer_hook_mint_fails_closed() {
    let authority = Pubkey::new_unique();
    assert_extension_mint_rejected(transfer_hook_mint(authority));
}
