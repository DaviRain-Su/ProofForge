mod common;

use {
    common::{harness, instruction, plain_account, slot, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const SELF_TRADE: u32 = 0x1004;
const STATE_LEN: usize = 1376;

struct PhoenixFixture {
    program_id: Pubkey,
    mollusk: Mollusk,
    state_key: Pubkey,
    state: Account,
}

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

impl PhoenixFixture {
    fn new(tick_size: u64) -> Self {
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
            &[tick_size],
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
        let mut init_accounts = vec![(state_key, state_account(&program_id, STATE_LEN))];
        init_accounts.extend(phoenix_accounts(
            trader_key,
            token_source,
            mint,
            token_destination,
            token_program,
        ));
        let initialized =
            mollusk.process_and_validate_instruction(&init, &init_accounts, &[Check::success()]);
        let state = resulting_state(initialized, &state_key);
        assert_eq!((slot(&state, 0), slot(&state, 1)), (1, tick_size));
        assert_eq!((slot(&state, 2), slot(&state, 3)), (1, 5));
        assert_eq!(
            (slot(&state, 54), slot(&state, 55), slot(&state, 56)),
            (0, 1, 1),
            "empty trader allocator state"
        );
        Self {
            program_id,
            mollusk,
            state_key,
            state,
        }
    }

    fn invocation(
        &self,
        trader_key: Pubkey,
        name: &str,
        params: &[u64],
        trader_signer: bool,
        state_signer: bool,
        state: Account,
    ) -> (solana_instruction::Instruction, Vec<(Pubkey, Account)>) {
        let token_source = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let token_destination = Pubkey::new_unique();
        let token_program = Pubkey::new_unique();
        let ix = instruction(
            self.program_id,
            self.state_key,
            name,
            params,
            true,
            state_signer,
            phoenix_metas(
                trader_key,
                trader_signer,
                token_source,
                mint,
                token_destination,
                token_program,
            ),
        );
        let mut accounts = vec![(self.state_key, state)];
        accounts.extend(phoenix_accounts(
            trader_key,
            token_source,
            mint,
            token_destination,
            token_program,
        ));
        (ix, accounts)
    }

    fn run(&mut self, trader_key: Pubkey, name: &str, params: &[u64], expected: u64) {
        let (ix, accounts) =
            self.invocation(trader_key, name, params, true, true, self.state.clone());
        let result = self.mollusk.process_and_validate_instruction(
            &ix,
            &accounts,
            &[
                Check::success(),
                Check::return_data(&expected.to_le_bytes()),
            ],
        );
        self.state = resulting_state(result, &self.state_key);
    }

    fn run_error(
        &self,
        trader_key: Pubkey,
        name: &str,
        params: &[u64],
        trader_signer: bool,
        error: ProgramError,
    ) {
        let before = self.state.data.clone();
        let (ix, accounts) = self.invocation(
            trader_key,
            name,
            params,
            trader_signer,
            true,
            self.state.clone(),
        );
        self.mollusk.process_and_validate_instruction(
            &ix,
            &accounts,
            &[
                Check::err(error),
                Check::account(&self.state_key).data(&before).build(),
            ],
        );
    }

    fn slots<const N: usize>(&self, indices: [usize; N]) -> [u64; N] {
        indices.map(|index| slot(&self.state, index))
    }
}

#[test]
fn ask_lifecycle_buy_fee_withdraw_and_evict_run_on_chain() {
    let mut fixture = PhoenixFixture::new(1);
    let maker = Pubkey::new_unique();
    let taker = Pubkey::new_unique();

    fixture.run(maker, "depositFunds", &[8, 0], 1);
    assert_eq!(fixture.slots([54, 61, 89, 93, 99, 100]), [1, 1, 0, 8, 0, 8]);
    for (word, index) in [65usize, 69, 73, 77].into_iter().enumerate() {
        let offset = word * 8;
        let expected = u64::from_le_bytes(
            maker.to_bytes()[offset..offset + 8]
                .try_into()
                .expect("pubkey limb"),
        );
        assert_eq!(slot(&fixture.state, index), expected);
    }

    fixture.run(maker, "postAsk", &[10, 3, 11, 12, 0, 0], 3);
    assert_eq!(fixture.slots([6, 10, 14, 18]), [10, 1, 1, 3]);
    assert_eq!(fixture.slots([2, 89, 93, 99, 100]), [2, 3, 5, 3, 5]);
    assert_eq!(fixture.slots([110, 160]), [3, 1], "place event");

    fixture.run(maker, "reduceAsk", &[10, 1, 0], 0);
    fixture.run(maker, "reduceAsk", &[10, 1, 1], 1);
    assert_eq!(fixture.slots([18, 89, 93, 99, 100]), [2, 2, 6, 2, 6]);
    assert_eq!(fixture.slots([110, 160]), [4, 1], "reduce event");

    fixture.run(taker, "depositFunds", &[0, 100], 2);
    assert_eq!(
        fixture.slots([54, 62, 86, 94, 98, 100]),
        [2, 1, 100, 0, 100, 6]
    );

    fixture.run(taker, "swapBuy", &[0, 21, 22, 2, 10], 2);
    assert_eq!(fixture.slots([18, 89, 85, 86, 94]), [0, 0, 20, 79, 2]);
    assert_eq!(fixture.slots([5, 97, 98, 99, 100]), [1, 0, 99, 0, 8]);
    assert_eq!(
        fixture.slots([110, 120, 160]),
        [2, 6, 2],
        "fill and summary events"
    );

    fixture.run(maker, "collectFees", &[], 1);
    assert_eq!(fixture.slots([4, 5, 110, 160]), [1, 0, 7, 1]);

    fixture.run(maker, "withdrawQuote", &[100], 20);
    fixture.run(maker, "withdrawBase", &[100], 6);
    assert_eq!(fixture.slots([85, 93, 98, 100]), [0, 0, 79, 2]);

    fixture.run(maker, "evictSeat", &[], 1);
    assert_eq!(fixture.slots([54, 55, 56, 57, 61]), [1, 3, 1, 3, 0]);
    assert_eq!(fixture.slots([65, 69, 73, 77]), [0, 0, 0, 0]);
}

#[test]
fn bid_lifecycle_reduce_and_sell_run_on_chain() {
    let mut fixture = PhoenixFixture::new(1);
    let maker = Pubkey::new_unique();
    let taker = Pubkey::new_unique();

    fixture.run(maker, "depositFunds", &[0, 100], 1);
    fixture.run(maker, "postBid", &[12, 3, 31, 32, 0, 0], 3);
    assert_eq!(fixture.slots([30, 34, 38, 42]), [12, !1, 1, 3]);
    assert_eq!(fixture.slots([2, 81, 85, 97, 98]), [2, 36, 64, 36, 64]);

    fixture.run(maker, "reduceBid", &[12, !1, 0], 0);
    fixture.run(maker, "reduceBid", &[12, !1, 1], 1);
    assert_eq!(fixture.slots([42, 81, 85, 97, 98]), [2, 24, 76, 24, 76]);
    assert_eq!(fixture.slots([110, 160]), [4, 1], "reduce event");

    fixture.run(taker, "depositFunds", &[2, 0], 2);
    fixture.run(taker, "swapSell", &[0, 41, 42, 2, 12], 2);
    assert_eq!(fixture.slots([42, 81, 86, 93, 94]), [0, 0, 23, 2, 0]);
    assert_eq!(fixture.slots([5, 97, 98, 99, 100]), [1, 0, 99, 0, 2]);
    assert_eq!(
        fixture.slots([110, 120, 160]),
        [2, 6, 2],
        "fill and summary events"
    );
}

#[test]
fn slot_and_unix_time_in_force_expire_strictly_on_chain() {
    let mut fixture = PhoenixFixture::new(1);
    let maker = Pubkey::new_unique();
    let taker = Pubkey::new_unique();

    fixture.mollusk.warp_to_slot(100);
    fixture.mollusk.sysvars.clock.unix_timestamp = 1_000;
    fixture.run(maker, "depositFunds", &[4, 0], 1);
    fixture.run(taker, "depositFunds", &[0, 100], 2);

    fixture.run(maker, "postAsk", &[10, 2, 51, 52, 100, 0], 2);
    assert_eq!(
        fixture.slots([18, 22, 26, 110, 120, 160]),
        [2, 100, 0, 3, 8, 2]
    );
    fixture.mollusk.warp_to_slot(101);
    fixture.run(taker, "swapBuy", &[0, 61, 62, 1, 10], 0);
    assert_eq!(fixture.slots([18, 89, 93, 99, 100]), [0, 0, 4, 0, 4]);
    assert_eq!(fixture.slots([110, 120, 160]), [9, 6, 2]);

    fixture.run(maker, "postAsk", &[11, 2, 71, 72, 0, 1_000], 2);
    assert_eq!(
        fixture.slots([18, 22, 26, 110, 120, 160]),
        [2, 0, 1_000, 3, 8, 2]
    );
    fixture.mollusk.sysvars.clock.unix_timestamp = 1_001;
    fixture.run(taker, "swapBuy", &[0, 81, 82, 1, 11], 0);
    assert_eq!(fixture.slots([18, 89, 93, 99, 100]), [0, 0, 4, 0, 4]);
    assert_eq!(fixture.slots([110, 120, 160]), [9, 6, 2]);
}

#[test]
fn all_self_trade_behaviors_run_on_chain() {
    let trader = Pubkey::new_unique();

    let mut abort = PhoenixFixture::new(1);
    abort.run(trader, "depositFunds", &[3, 100], 1);
    abort.run(trader, "postAsk", &[10, 3, 0, 0, 0, 0], 3);
    abort.run_error(
        trader,
        "swapBuy",
        &[0, 0, 0, 2, 10],
        true,
        ProgramError::Custom(SELF_TRADE),
    );
    assert_eq!(abort.slots([18, 89, 93, 110, 160]), [3, 3, 0, 3, 1]);

    let mut cancel_provide = PhoenixFixture::new(1);
    cancel_provide.run(trader, "depositFunds", &[3, 100], 1);
    cancel_provide.run(trader, "postAsk", &[10, 3, 0, 0, 0, 0], 3);
    cancel_provide.run(trader, "swapBuy", &[1, 0, 0, 2, 10], 0);
    assert_eq!(cancel_provide.slots([18, 89, 93, 99, 100]), [0, 0, 3, 0, 3]);
    assert_eq!(cancel_provide.slots([110, 120, 160]), [4, 6, 2]);

    let mut decrement_take = PhoenixFixture::new(1);
    decrement_take.run(trader, "depositFunds", &[3, 100], 1);
    decrement_take.run(trader, "postAsk", &[10, 3, 0, 0, 0, 0], 3);
    decrement_take.run(trader, "swapBuy", &[2, 0, 0, 2, 10], 0);
    assert_eq!(decrement_take.slots([18, 89, 93, 99, 100]), [1, 1, 2, 1, 2]);
    assert_eq!(decrement_take.slots([110, 120, 160]), [4, 6, 2]);
}

#[test]
fn signer_and_state_owner_failures_are_atomic() {
    let fixture = PhoenixFixture::new(1);
    let trader = Pubkey::new_unique();

    fixture.run_error(
        trader,
        "depositFunds",
        &[1, 0],
        false,
        ProgramError::Custom(1),
    );

    let mut forged = fixture.state.clone();
    forged.owner = Pubkey::new_unique();
    let before = forged.data.clone();
    let (ix, accounts) = fixture.invocation(trader, "depositFunds", &[1, 0], true, true, forged);
    fixture.mollusk.process_and_validate_instruction(
        &ix,
        &accounts,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&fixture.state_key).data(&before).build(),
        ],
    );
}
