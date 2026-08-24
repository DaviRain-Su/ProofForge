mod common;

use {
    common::{harness, instruction, plain_account, slot, state_account},
    mollusk_svm::result::Check,
    solana_instruction::AccountMeta,
    solana_pubkey::Pubkey,
};

fn resulting_state(
    result: mollusk_svm::result::InstructionResult,
    state_key: &Pubkey,
) -> solana_account::Account {
    result
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == state_key)
        .expect("resulting state")
        .1
}

fn phoenix_metas(
    trader_key: Pubkey,
    trader_signer: bool,
    token_source: Pubkey,
    mint: Pubkey,
    token_destination: Pubkey,
    token_program: Pubkey,
) -> Vec<AccountMeta> {
    vec![
        AccountMeta::new_readonly(trader_key, trader_signer),
        AccountMeta::new(token_source, false),
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new(token_destination, false),
        AccountMeta::new_readonly(token_program, false),
    ]
}

fn phoenix_accounts(
    trader_key: Pubkey,
    token_source: Pubkey,
    mint: Pubkey,
    token_destination: Pubkey,
    token_program: Pubkey,
) -> Vec<(Pubkey, solana_account::Account)> {
    vec![
        (trader_key, plain_account()),
        (token_source, plain_account()),
        (mint, plain_account()),
        (token_destination, plain_account()),
        (token_program, plain_account()),
    ]
}

#[test]
fn authenticated_deposit_and_post_ask_run_on_chain() {
    let (program_id, mollusk) = harness("Phoenix", "PF_PHOENIX_SO");
    let state_key = Pubkey::new_unique();
    let trader_key = Pubkey::new_unique();
    let token_source = Pubkey::new_unique();
    let mint = Pubkey::new_unique();
    let token_destination = Pubkey::new_unique();
    let token_program = Pubkey::new_unique();

    let init = instruction(
        program_id,
        state_key,
        "initialize",
        &[100],
        true,
        true,
        phoenix_metas(
            trader_key,
            false,
            token_source,
            mint,
            token_destination,
            token_program,
        ),
    );
    let mut init_accounts = vec![(state_key, state_account(&program_id, 1376))];
    init_accounts.extend(phoenix_accounts(
        trader_key,
        token_source,
        mint,
        token_destination,
        token_program,
    ));
    let initialized =
        mollusk.process_and_validate_instruction(&init, &init_accounts, &[Check::success()]);
    let account = resulting_state(initialized, &state_key);
    assert_eq!((slot(&account, 0), slot(&account, 1)), (1, 100));
    assert_eq!((slot(&account, 2), slot(&account, 3)), (1, 5));
    assert_eq!(
        (slot(&account, 54), slot(&account, 55), slot(&account, 56)),
        (0, 1, 1),
        "empty trader allocator state"
    );

    let deposit = instruction(
        program_id,
        state_key,
        "depositFunds",
        &[7, 9],
        true,
        false,
        phoenix_metas(
            trader_key,
            true,
            token_source,
            mint,
            token_destination,
            token_program,
        ),
    );
    let mut deposit_accounts = vec![(state_key, account)];
    deposit_accounts.extend(phoenix_accounts(
        trader_key,
        token_source,
        mint,
        token_destination,
        token_program,
    ));
    let deposited = mollusk.process_and_validate_instruction(
        &deposit,
        &deposit_accounts,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    let account = resulting_state(deposited, &state_key);
    assert_eq!((slot(&account, 54), slot(&account, 61)), (1, 1));
    assert_eq!((slot(&account, 85), slot(&account, 93)), (9, 7));
    for (word, index) in [65usize, 69, 73, 77].into_iter().enumerate() {
        let offset = word * 8;
        let expected = u64::from_le_bytes(
            trader_key.to_bytes()[offset..offset + 8]
                .try_into()
                .expect("pubkey limb"),
        );
        assert_eq!(slot(&account, index), expected);
    }

    let post = instruction(
        program_id,
        state_key,
        "postAsk",
        &[50, 3, 11, 12, 0, 0],
        true,
        false,
        phoenix_metas(
            trader_key,
            true,
            token_source,
            mint,
            token_destination,
            token_program,
        ),
    );
    let mut post_accounts = vec![(state_key, account)];
    post_accounts.extend(phoenix_accounts(
        trader_key,
        token_source,
        mint,
        token_destination,
        token_program,
    ));
    let posted = mollusk.process_and_validate_instruction(
        &post,
        &post_accounts,
        &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
    );
    let account = resulting_state(posted, &state_key);
    assert_eq!(
        (slot(&account, 6), slot(&account, 14), slot(&account, 18)),
        (50, 1, 3)
    );
    assert_eq!((slot(&account, 89), slot(&account, 93)), (3, 4));
    assert_eq!(slot(&account, 2), 2, "sequence advanced");
    assert_eq!(slot(&account, 160), 1, "place event recorded");
}
