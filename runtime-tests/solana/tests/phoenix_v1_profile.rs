mod common;

use {
    mollusk_svm::result::Check, solana_account::Account, solana_instruction::AccountMeta,
    solana_native_token::LAMPORTS_PER_SOL, solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const MARKET_HEADER_DISCRIMINANT: u64 = 8_167_313_896_524_341_111;
const SMALLEST_MARKET_BYTES: usize = 84_944;
const OFFICIAL_PROFILES: [(u64, u64, u64, usize); 12] = [
    (512, 512, 128, 84_944),
    (512, 512, 1025, 214_112),
    (512, 512, 1153, 232_544),
    (1024, 1024, 128, 150_480),
    (1024, 1024, 2049, 427_104),
    (1024, 1024, 2177, 445_536),
    (2048, 2048, 128, 281_552),
    (2048, 2048, 4097, 853_088),
    (2048, 2048, 4225, 871_520),
    (4096, 4096, 128, 543_696),
    (4096, 4096, 8193, 1_705_056),
    (4096, 4096, 8321, 1_723_488),
];
const PHOENIX_PROGRAM: Pubkey = Pubkey::new_from_array([
    13, 120, 199, 140, 143, 36, 144, 159, 45, 74, 23, 85, 191, 50, 60, 30, 241, 134, 34, 139, 58,
    179, 231, 224, 138, 152, 105, 153, 121, 58, 159, 22,
]);

fn market_account(
    owner: Pubkey,
    data_len: usize,
    discriminant: u64,
    bids: u64,
    asks: u64,
    seats: u64,
) -> Account {
    let mut account = Account::new(10 * LAMPORTS_PER_SOL, data_len, &owner);
    if data_len >= 40 {
        account.data[0..8].copy_from_slice(&discriminant.to_le_bytes());
        account.data[16..24].copy_from_slice(&bids.to_le_bytes());
        account.data[24..32].copy_from_slice(&asks.to_le_bytes());
        account.data[32..40].copy_from_slice(&seats.to_le_bytes());
    }
    account
}

fn write_word(account: &mut Account, word: usize, value: u64) {
    let offset = 8 * word;
    account.data[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn packed_u32(low: u32, high: u32) -> u64 {
    u64::from(low) | (u64::from(high) << 32)
}

fn write_allocator_header(
    account: &mut Account,
    root_word: usize,
    size: u64,
    root: u32,
    bump_index: u32,
    free_list_head: u32,
) {
    write_word(account, root_word, u64::from(root));
    write_word(account, root_word + 1, 0);
    write_word(account, root_word + 2, size);
    write_word(
        account,
        root_word + 3,
        packed_u32(bump_index, free_list_head),
    );
}

fn write_order_node(
    account: &mut Account,
    tree_root_word: usize,
    index: usize,
    left: u32,
    right: u32,
    parent: u32,
    color: u32,
    price: u64,
    sequence: u64,
) {
    assert!(index > 0);
    let slot_word = tree_root_word + 4 + 8 * (index - 1);
    write_word(account, slot_word, packed_u32(left, right));
    write_word(account, slot_word + 1, packed_u32(parent, color));
    write_word(account, slot_word + 2, price);
    write_word(account, slot_word + 3, sequence);
}

fn body_count_words(book_capacity: u64) -> (usize, usize) {
    match book_capacity {
        512 => (4212, 8312),
        1024 => (8308, 16504),
        2048 => (16500, 32888),
        4096 => (32884, 65656),
        _ => panic!("unsupported book capacity {book_capacity}"),
    }
}

fn tree_root_words(book_capacity: u64) -> (usize, usize) {
    let (ask_count, trader_count) = body_count_words(book_capacity);
    (ask_count - 2, trader_count - 2)
}

fn run_view(name: &str, market: Account, checks: &[Check]) {
    let (program_id, mollusk) = common::harness("PhoenixV1Profile", "PF_PHOENIX_V1_PROFILE_SO");
    let state_key = common::dummy_state_key(&program_id);
    let market_key = Pubkey::new_unique();
    let instruction = common::instruction(
        program_id,
        state_key,
        name,
        &[],
        false,
        false,
        vec![AccountMeta::new_readonly(market_key, false)],
    );
    mollusk.process_and_validate_instruction(
        &instruction,
        &[
            (state_key, common::dummy_state_account(&program_id)),
            (market_key, market),
        ],
        checks,
    );
}

#[test]
fn all_official_profiles_select_exact_account_size() {
    for (bids, asks, seats, expected) in OFFICIAL_PROFILES {
        let mut market = market_account(
            PHOENIX_PROGRAM,
            expected,
            MARKET_HEADER_DISCRIMINANT,
            bids,
            asks,
            seats,
        );
        let (ask_count_word, trader_count_word) = body_count_words(bids);
        let (ask_root_word, trader_root_word) = tree_root_words(bids);
        write_word(&mut market, 106, 777);
        write_allocator_header(&mut market, 110, 1, 1, 2, 2);
        write_allocator_header(&mut market, ask_root_word, 2, 1, 3, 3);
        write_allocator_header(&mut market, trader_root_word, 3, 1, 4, 4);
        write_order_node(&mut market, 110, 1, 0, 0, 0, 0, 999, !1u64);
        assert_eq!(ask_count_word, ask_root_word + 2);
        assert_eq!(trader_count_word, trader_root_word + 2);
        run_view(
            "profileAccountBytes",
            market.clone(),
            &[
                Check::success(),
                Check::return_data(&(expected as u64).to_le_bytes()),
            ],
        );
        run_view(
            "marketSequence",
            market.clone(),
            &[Check::success(), Check::return_data(&777u64.to_le_bytes())],
        );
        run_view(
            "bodyEntryCount",
            market.clone(),
            &[Check::success(), Check::return_data(&6u64.to_le_bytes())],
        );
        run_view(
            "allocatorHeadersValid",
            market.clone(),
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
        run_view(
            "bidRootNeighborhoodValid",
            market,
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
    }

    let smallest = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    run_view(
        "headerSeats",
        smallest,
        &[Check::success(), Check::return_data(&128u64.to_le_bytes())],
    );
}

#[test]
fn noncanonical_owner_discriminant_profile_or_length_is_rejected() {
    for market in [
        market_account(
            Pubkey::new_unique(),
            SMALLEST_MARKET_BYTES,
            MARKET_HEADER_DISCRIMINANT,
            512,
            512,
            128,
        ),
        market_account(PHOENIX_PROGRAM, SMALLEST_MARKET_BYTES, 7, 512, 512, 128),
        market_account(
            PHOENIX_PROGRAM,
            SMALLEST_MARKET_BYTES,
            MARKET_HEADER_DISCRIMINANT,
            512,
            512,
            129,
        ),
        market_account(
            PHOENIX_PROGRAM,
            SMALLEST_MARKET_BYTES - 8,
            MARKET_HEADER_DISCRIMINANT,
            512,
            512,
            128,
        ),
    ] {
        run_view(
            "profileAccountBytes",
            market,
            &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
        );
    }

    for (word, value) in [(112, 513), (4212, 513), (8312, 129)] {
        let mut malformed = market_account(
            PHOENIX_PROGRAM,
            SMALLEST_MARKET_BYTES,
            MARKET_HEADER_DISCRIMINANT,
            512,
            512,
            128,
        );
        write_word(&mut malformed, word, value);
        run_view(
            "bodyEntryCount",
            malformed,
            &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
        );
    }

    for (word, value) in [
        (110, 513),
        (111, 1),
        (113, packed_u32(0, 0)),
        (4210, 0),
        (4213, packed_u32(2, 3)),
        (8313, packed_u32(130, 130)),
    ] {
        let mut malformed = market_account(
            PHOENIX_PROGRAM,
            SMALLEST_MARKET_BYTES,
            MARKET_HEADER_DISCRIMINANT,
            512,
            512,
            128,
        );
        write_allocator_header(&mut malformed, 110, 1, 1, 2, 2);
        write_allocator_header(&mut malformed, 4210, 1, 1, 2, 2);
        write_allocator_header(&mut malformed, 8310, 1, 1, 2, 2);
        write_word(&mut malformed, word, value);
        run_view(
            "allocatorHeadersValid",
            malformed,
            &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
        );
    }
}

#[test]
fn short_header_word_read_fails_closed() {
    let market = market_account(PHOENIX_PROGRAM, 32, MARKET_HEADER_DISCRIMINANT, 0, 0, 0);
    run_view(
        "headerSeats",
        market,
        &[Check::err(ProgramError::Custom(1))],
    );
}

#[test]
fn bid_root_uses_bounded_account_resident_slot_index() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 1, 2, 3, 1);
    write_allocator_header(&mut market, 4210, 0, 0, 1, 1);
    write_allocator_header(&mut market, 8310, 0, 0, 1, 1);
    write_word(&mut market, 114, 3);
    write_order_node(&mut market, 110, 2, 0, 0, 0, 0, 999, !1u64);
    run_view(
        "bidRootPrice",
        market.clone(),
        &[Check::success(), Check::return_data(&999u64.to_le_bytes())],
    );

    write_order_node(&mut market, 110, 2, 3, 0, 0, 0, 999, !1u64);
    run_view(
        "bidRootPrice",
        market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    write_order_node(&mut market, 110, 2, 0, 0, 0, 1, 999, !1u64);
    run_view(
        "bidRootPrice",
        market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    write_allocator_header(&mut market, 110, 3, 2, 4, 4);
    write_order_node(&mut market, 110, 1, 0, 0, 2, 1, 110, !2u64);
    write_order_node(&mut market, 110, 2, 1, 3, 0, 0, 100, !1u64);
    write_order_node(&mut market, 110, 3, 0, 0, 2, 0, 90, !3u64);
    run_view(
        "bidRootNeighborhoodValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    write_order_node(&mut market, 110, 1, 0, 0, 3, 1, 110, !2u64);
    run_view(
        "bidRootNeighborhoodValid",
        market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    write_order_node(&mut market, 110, 1, 0, 0, 2, 2, 110, !2u64);
    run_view(
        "bidRootNeighborhoodValid",
        market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    write_order_node(&mut market, 110, 1, 0, 0, 2, 1, 80, !2u64);
    run_view(
        "bidRootNeighborhoodValid",
        market,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}
