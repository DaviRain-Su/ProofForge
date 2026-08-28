//! Canonical program-id and allocation-free SPL Token base-state view gates.

mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_pubkey::Pubkey,
    spl_token_interface::state::{Account as TokenAccount, AccountState, Mint},
};

const AMOUNT: u64 = 0x0102_0304_0506_0708;
const SUPPLY: u64 = 0x1122_3344_5566_7788;
const DECIMALS: u8 = 9;

fn harness() -> (Pubkey, Mollusk) {
    let (program_id, mut mollusk) = common::harness("TokenStateView", "PF_TOKEN_STATE_VIEW_SO");
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn token_account(mint: Pubkey, authority: Pubkey, state: AccountState) -> Account {
    token::create_account_for_token_account(TokenAccount {
        mint,
        owner: authority,
        amount: AMOUNT,
        delegate: None.into(),
        state,
        is_native: None.into(),
        delegated_amount: 0,
        close_authority: None.into(),
    })
}

fn mint_account(authority: Pubkey) -> Account {
    token::create_account_for_mint(Mint {
        mint_authority: Some(authority).into(),
        supply: SUPPLY,
        decimals: DECIMALS,
        is_initialized: true,
        freeze_authority: None.into(),
    })
}

fn accounts(
    program_id: &Pubkey,
    state: AccountState,
) -> (Vec<AccountMeta>, Vec<(Pubkey, Account)>) {
    let state_key = common::dummy_state_key(program_id);
    let authority = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let token_state = Pubkey::new_unique();
    let (token_id, token_program) = token::keyed_account();
    let metas = vec![
        AccountMeta::new_readonly(token_id, false),
        AccountMeta::new_readonly(token_state, false),
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new_readonly(authority, false),
    ];
    let keyed = vec![
        (state_key, common::dummy_state_account(program_id)),
        (token_id, token_program),
        (token_state, token_account(mint, authority, state)),
        (mint, mint_account(authority)),
        (authority, common::plain_account()),
    ];
    (metas, keyed)
}

fn expect(
    program_id: &Pubkey,
    mollusk: &Mollusk,
    name: &str,
    metas: Vec<AccountMeta>,
    accounts: Vec<(Pubkey, Account)>,
    expected: u64,
) {
    let ix = common::instruction(
        *program_id,
        common::dummy_state_key(program_id),
        name,
        &[],
        false,
        false,
        metas,
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::success(),
            Check::return_data(&expected.to_le_bytes()),
        ],
    );
}

#[test]
fn initialized_base_state_authenticates_and_decodes_exact_fields() {
    let (program_id, mollusk) = harness();
    let (metas, keyed) = accounts(&program_id, AccountState::Initialized);
    for (name, expected) in [
        ("programValid", 1),
        ("accountValid", 1),
        ("accountInitialized", 1),
        ("accountFrozen", 0),
        ("mintMatches", 1),
        ("authorityMatches", 1),
        ("amount", AMOUNT),
        ("mintValid", 1),
        ("mintInitialized", 1),
        ("supply", SUPPLY),
        ("decimals", u64::from(DECIMALS)),
    ] {
        expect(
            &program_id,
            &mollusk,
            name,
            metas.clone(),
            keyed.clone(),
            expected,
        );
    }
}

#[test]
fn frozen_is_initialized_but_not_ordinary_state() {
    let (program_id, mollusk) = harness();
    let (metas, keyed) = accounts(&program_id, AccountState::Frozen);
    expect(
        &program_id,
        &mollusk,
        "accountInitialized",
        metas.clone(),
        keyed.clone(),
        1,
    );
    expect(&program_id, &mollusk, "accountFrozen", metas, keyed, 1);
}

#[test]
fn wrong_program_identity_and_owner_fail_closed() {
    let (program_id, mollusk) = harness();
    let (mut metas, mut keyed) = accounts(&program_id, AccountState::Initialized);

    let fake_program_id = Pubkey::new_unique();
    let mut fake_program = Account::default();
    fake_program.executable = true;
    metas[0] = AccountMeta::new_readonly(fake_program_id, false);
    keyed[1] = (fake_program_id, fake_program);
    expect(
        &program_id,
        &mollusk,
        "programValid",
        metas.clone(),
        keyed.clone(),
        0,
    );

    let (metas, mut keyed) = accounts(&program_id, AccountState::Initialized);
    keyed[2].1.owner = Pubkey::new_unique();
    expect(&program_id, &mollusk, "accountValid", metas, keyed, 0);
}

#[test]
fn malformed_state_and_mint_tags_fail_closed() {
    let (program_id, mollusk) = harness();
    let (metas, mut keyed) = accounts(&program_id, AccountState::Initialized);

    // Account.state is byte 108. Values above Frozen(2) are invalid packed enums.
    keyed[2].1.data[108] = 3;
    expect(
        &program_id,
        &mollusk,
        "accountValid",
        metas.clone(),
        keyed.clone(),
        0,
    );

    // Mint.is_initialized is byte 45 and must be a canonical zero/one byte.
    keyed[3].1.data[45] = 2;
    expect(&program_id, &mollusk, "mintValid", metas, keyed, 0);
}
