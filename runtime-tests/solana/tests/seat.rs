mod common;

use {
    common::{harness, instruction, plain_account, state_account},
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    solana_account::Account,
    solana_instruction::{error::InstructionError, AccountMeta},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    spl_token_interface::state::Mint,
};

const STATE_LEN: usize = 16;
const SEAT_SPACE: usize = 16;
const CREATE_LAMPORTS: u64 = LAMPORTS_PER_SOL;
const PAYER_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const TOKEN_ACCOUNT_LEN: usize = 165;
const DECIMALS: u8 = 6;

struct SeatFixture {
    program_id: Pubkey,
    mollusk: Mollusk,
    state_key: Pubkey,
    state: Account,
}

fn resulting_account(result: mollusk_svm::result::InstructionResult, key: &Pubkey) -> Account {
    result
        .resulting_accounts
        .into_iter()
        .find(|(actual, _)| actual == key)
        .expect("resulting account")
        .1
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
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

fn uninitialized_token_account() -> Account {
    Account::new(
        Rent::default().minimum_balance(TOKEN_ACCOUNT_LEN),
        TOKEN_ACCOUNT_LEN,
        &token::ID,
    )
}

impl SeatFixture {
    fn new() -> Self {
        let (program_id, mut mollusk) = harness("Seat", "PF_SEAT_SO");
        token::add_program(&mut mollusk);
        let state_key = Pubkey::new_unique();
        let extras = [
            Pubkey::new_unique(),
            Pubkey::new_unique(),
            Pubkey::new_unique(),
            Pubkey::new_unique(),
        ];
        let init = instruction(
            program_id,
            state_key,
            "initialize",
            &[0],
            true,
            true,
            extras
                .iter()
                .map(|key| AccountMeta::new_readonly(*key, false))
                .collect(),
        );
        let mut accounts = vec![(state_key, state_account(&program_id, STATE_LEN))];
        accounts.extend(extras.iter().map(|key| (*key, plain_account())));
        let initialized =
            mollusk.process_and_validate_instruction(&init, &accounts, &[Check::success()]);
        let state = resulting_account(initialized, &state_key);
        Self {
            program_id,
            mollusk,
            state_key,
            state,
        }
    }

    fn initialize_vault(&self, entry: &str, owner: Pubkey, mint: Pubkey) -> Account {
        let vault = Pubkey::new_unique();
        let (token_program, token_account) = token::keyed_account();
        let ix = instruction(
            self.program_id,
            self.state_key,
            entry,
            &[],
            true,
            true,
            vec![
                AccountMeta::new_readonly(owner, false),
                AccountMeta::new(vault, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new_readonly(token_program, false),
            ],
        );
        let accounts = vec![
            (self.state_key, self.state.clone()),
            (owner, funded(LAMPORTS_PER_SOL)),
            (vault, uninitialized_token_account()),
            (mint, mint_account(owner)),
            (token_program, token_account),
        ];
        let result = self.mollusk.process_and_validate_instruction(
            &ix,
            &accounts,
            &[
                Check::success(),
                Check::return_data(&0u64.to_le_bytes()),
                Check::account(&vault)
                    .owner(&token::ID)
                    .space(TOKEN_ACCOUNT_LEN)
                    .data_slice(0, mint.as_ref())
                    .data_slice(32, owner.as_ref())
                    .build(),
            ],
        );
        resulting_account(result, &vault)
    }
}

#[test]
fn pda_view_runs_with_walk_prelude() {
    let fixture = SeatFixture::new();
    let extras = [
        Pubkey::new_unique(),
        Pubkey::new_unique(),
        Pubkey::new_unique(),
        Pubkey::new_unique(),
    ];
    let bump = Pubkey::find_program_address(&[b"vault"], &fixture.program_id).1 as u64;
    let get = instruction(
        fixture.program_id,
        fixture.state_key,
        "get",
        &[],
        false,
        false,
        extras
            .iter()
            .map(|key| AccountMeta::new_readonly(*key, false))
            .collect(),
    );
    let mut accounts = vec![(fixture.state_key, fixture.state)];
    accounts.extend(extras.iter().map(|key| (*key, plain_account())));
    fixture.mollusk.process_and_validate_instruction(
        &get,
        &accounts,
        &[Check::success(), Check::return_data(&bump.to_le_bytes())],
    );
}

#[test]
fn open_seat_creates_the_canonical_pda() {
    let fixture = SeatFixture::new();
    let payer = Pubkey::new_unique();
    let (seat, bump) = Pubkey::find_program_address(&[b"vault"], &fixture.program_id);
    assert!((1..=255).contains(&bump));
    let (system_program, system_account) = mollusk_svm::program::keyed_account_for_system_program();
    let unused = Pubkey::new_unique();
    let ix = instruction(
        fixture.program_id,
        fixture.state_key,
        "openSeat",
        &[CREATE_LAMPORTS],
        true,
        true,
        vec![
            AccountMeta::new(payer, true),
            AccountMeta::new(seat, false),
            AccountMeta::new_readonly(system_program, false),
            AccountMeta::new_readonly(unused, false),
        ],
    );
    fixture.mollusk.process_and_validate_instruction(
        &ix,
        &[
            (fixture.state_key, fixture.state),
            (payer, funded(PAYER_LAMPORTS)),
            (seat, funded(0)),
            (system_program, system_account),
            (unused, plain_account()),
        ],
        &[
            Check::success(),
            Check::return_data(&CREATE_LAMPORTS.to_le_bytes()),
            Check::account(&payer)
                .lamports(PAYER_LAMPORTS - CREATE_LAMPORTS)
                .build(),
            Check::account(&seat)
                .lamports(CREATE_LAMPORTS)
                .owner(&fixture.program_id)
                .space(SEAT_SPACE)
                .build(),
        ],
    );
}

#[test]
fn open_seat_missing_payer_signature_is_atomic() {
    let fixture = SeatFixture::new();
    let payer = Pubkey::new_unique();
    let (seat, _) = Pubkey::find_program_address(&[b"vault"], &fixture.program_id);
    let (system_program, system_account) = mollusk_svm::program::keyed_account_for_system_program();
    let unused = Pubkey::new_unique();
    let ix = instruction(
        fixture.program_id,
        fixture.state_key,
        "openSeat",
        &[CREATE_LAMPORTS],
        true,
        true,
        vec![
            AccountMeta::new(payer, false),
            AccountMeta::new(seat, false),
            AccountMeta::new_readonly(system_program, false),
            AccountMeta::new_readonly(unused, false),
        ],
    );
    let result = fixture.mollusk.process_instruction(
        &ix,
        &[
            (fixture.state_key, fixture.state),
            (payer, funded(PAYER_LAMPORTS)),
            (seat, funded(0)),
            (system_program, system_account),
            (unused, plain_account()),
        ],
    );
    assert!(
        matches!(
            result.raw_result,
            Err(InstructionError::PrivilegeEscalation)
        ),
        "missing payer signature must reject the CPI: {:?}",
        result.program_result
    );
    let payer_after = result
        .resulting_accounts
        .iter()
        .find(|(key, _)| key == &payer)
        .expect("payer after failed CPI")
        .1
        .clone();
    let seat_after = result
        .resulting_accounts
        .iter()
        .find(|(key, _)| key == &seat)
        .expect("seat after failed CPI")
        .1
        .clone();
    assert_eq!(payer_after.lamports, PAYER_LAMPORTS);
    assert_eq!(seat_after.lamports, 0);
    assert_eq!(seat_after.data.len(), 0);
}

#[test]
fn base_and_quote_vaults_initialize_without_owner_signature() {
    let fixture = SeatFixture::new();
    let owner = Pubkey::new_unique();
    let base_mint = Pubkey::new_unique();
    let quote_mint = Pubkey::new_unique();

    let base_vault = fixture.initialize_vault("openBase", owner, base_mint);
    let quote_vault = fixture.initialize_vault("openQuote", owner, quote_mint);

    assert_eq!(&base_vault.data[..32], base_mint.as_ref());
    assert_eq!(&quote_vault.data[..32], quote_mint.as_ref());
    assert_eq!(&base_vault.data[32..64], owner.as_ref());
    assert_eq!(&quote_vault.data[32..64], owner.as_ref());
}

#[test]
fn vault_must_be_writable_and_failure_is_atomic() {
    let fixture = SeatFixture::new();
    let owner = Pubkey::new_unique();
    let vault = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let (token_program, token_account) = token::keyed_account();
    let before = uninitialized_token_account();
    let before_data = before.data.clone();
    let ix = instruction(
        fixture.program_id,
        fixture.state_key,
        "openBase",
        &[],
        true,
        true,
        vec![
            AccountMeta::new_readonly(owner, false),
            AccountMeta::new_readonly(vault, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(token_program, false),
        ],
    );
    fixture.mollusk.process_and_validate_instruction(
        &ix,
        &[
            (fixture.state_key, fixture.state),
            (owner, funded(LAMPORTS_PER_SOL)),
            (vault, before),
            (mint, mint_account(owner)),
            (token_program, token_account),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&vault).data(&before_data).build(),
        ],
    );
}
