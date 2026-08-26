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

fn write_free_order_slot(account: &mut Account, tree_root_word: usize, index: usize, next: u32) {
    assert!(index > 0);
    let slot_word = tree_root_word + 4 + 8 * (index - 1);
    write_word(account, slot_word, u64::from(next));
}

fn write_perfect_bid_tree(
    account: &mut Account,
    tree_root_word: usize,
    index: u32,
    last_index: u32,
    parent: u32,
    rank: &mut u64,
) {
    let left = index.checked_mul(2).filter(|child| *child <= last_index);
    let right = index
        .checked_mul(2)
        .and_then(|child| child.checked_add(1))
        .filter(|child| *child <= last_index);
    if let Some(left) = left {
        write_perfect_bid_tree(account, tree_root_word, left, last_index, index, rank);
    }
    let price = u64::from(last_index) - *rank;
    *rank += 1;
    write_order_node(
        account,
        tree_root_word,
        index as usize,
        left.unwrap_or(0),
        right.unwrap_or(0),
        parent,
        0,
        price,
        !u64::from(index),
    );
    if let Some(right) = right {
        write_perfect_bid_tree(account, tree_root_word, right, last_index, index, rank);
    }
}

fn write_perfect_ask_tree(
    account: &mut Account,
    tree_root_word: usize,
    index: u32,
    last_index: u32,
    parent: u32,
    rank: &mut u64,
) {
    let left = index.checked_mul(2).filter(|child| *child <= last_index);
    let right = index
        .checked_mul(2)
        .and_then(|child| child.checked_add(1))
        .filter(|child| *child <= last_index);
    if let Some(left) = left {
        write_perfect_ask_tree(account, tree_root_word, left, last_index, index, rank);
    }
    *rank += 1;
    write_order_node(
        account,
        tree_root_word,
        index as usize,
        left.unwrap_or(0),
        right.unwrap_or(0),
        parent,
        0,
        *rank,
        u64::from(index),
    );
    if let Some(right) = right {
        write_perfect_ask_tree(account, tree_root_word, right, last_index, index, rank);
    }
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

fn run_view_args(name: &str, args: &[u64], market: Account, checks: &[Check]) {
    let (program_id, mollusk) = common::harness("PhoenixV1Profile", "PF_PHOENIX_V1_PROFILE_SO");
    let state_key = common::dummy_state_key(&program_id);
    let market_key = Pubkey::new_unique();
    let instruction = common::instruction(
        program_id,
        state_key,
        name,
        args,
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

fn run_view(name: &str, market: Account, checks: &[Check]) {
    run_view_args(name, &[], market, checks);
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
        write_order_node(&mut market, ask_root_word, 1, 0, 2, 0, 0, 100, 1);
        write_order_node(&mut market, ask_root_word, 2, 0, 0, 1, 1, 110, 2);
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
        run_view_args(
            "bidParentPathValid",
            &[1],
            market.clone(),
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
        run_view(
            "bidTreeValid",
            market.clone(),
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
        run_view(
            "askTreeValid",
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

#[test]
fn bid_parent_path_is_bounded_and_reciprocal() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 3, 2, 4, 4);
    write_allocator_header(&mut market, 4210, 0, 0, 1, 1);
    write_allocator_header(&mut market, 8310, 0, 0, 1, 1);
    write_order_node(&mut market, 110, 1, 0, 0, 2, 1, 110, !2u64);
    write_order_node(&mut market, 110, 2, 1, 3, 0, 0, 100, !1u64);
    write_order_node(&mut market, 110, 3, 0, 0, 2, 0, 90, !3u64);

    for index in [1, 2, 3] {
        run_view_args(
            "bidParentPathValid",
            &[index],
            market.clone(),
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
    }
    for index in [0, 4] {
        run_view_args(
            "bidParentPathValid",
            &[index],
            market.clone(),
            &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
        );
    }

    write_order_node(&mut market, 110, 1, 0, 0, 3, 1, 110, !2u64);
    run_view_args(
        "bidParentPathValid",
        &[1],
        market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    // A reciprocal 1 ↔ 3 parent cycle excludes root 2. It cannot loop forever: the emitted
    // constant-memory walk returns zero after its static 32-edge bound.
    write_order_node(&mut market, 110, 1, 3, 0, 3, 1, 110, !2u64);
    write_order_node(&mut market, 110, 2, 0, 0, 0, 0, 100, !1u64);
    write_order_node(&mut market, 110, 3, 1, 0, 1, 0, 90, !3u64);
    run_view_args(
        "bidParentPathValid",
        &[1],
        market,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn bid_tree_validates_whole_tree_and_allocator_partition() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 3, 2, 5, 4);
    write_allocator_header(&mut market, 4210, 0, 0, 1, 1);
    write_allocator_header(&mut market, 8310, 0, 0, 1, 1);
    write_order_node(&mut market, 110, 1, 0, 0, 2, 1, 110, !2u64);
    write_order_node(&mut market, 110, 2, 1, 3, 0, 0, 100, !1u64);
    write_order_node(&mut market, 110, 3, 0, 0, 2, 1, 90, !3u64);
    write_free_order_slot(&mut market, 110, 4, 5);
    run_view(
        "bidTreeValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let mut fully_recycled = market.clone();
    write_allocator_header(&mut fully_recycled, 110, 0, 0, 4, 1);
    write_free_order_slot(&mut fully_recycled, 110, 1, 2);
    write_free_order_slot(&mut fully_recycled, 110, 2, 3);
    write_free_order_slot(&mut fully_recycled, 110, 3, 4);
    run_view(
        "bidTreeValid",
        fully_recycled.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    write_free_order_slot(&mut fully_recycled, 110, 1, 3);
    run_view(
        "bidTreeValid",
        fully_recycled,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut wrong_order = market.clone();
    write_order_node(&mut wrong_order, 110, 1, 0, 0, 2, 1, 80, !2u64);
    run_view(
        "bidTreeValid",
        wrong_order,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut red_red_edge = market.clone();
    write_allocator_header(&mut red_red_edge, 110, 4, 2, 6, 5);
    write_order_node(&mut red_red_edge, 110, 1, 0, 4, 2, 1, 110, !2u64);
    write_order_node(&mut red_red_edge, 110, 4, 0, 0, 1, 1, 105, !4u64);
    write_free_order_slot(&mut red_red_edge, 110, 5, 6);
    run_view(
        "bidTreeValid",
        red_red_edge,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut unequal_black_height = market.clone();
    write_order_node(&mut unequal_black_height, 110, 1, 0, 0, 2, 0, 110, !2u64);
    run_view(
        "bidTreeValid",
        unequal_black_height,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut live_free_overlap = market.clone();
    write_allocator_header(&mut live_free_overlap, 110, 3, 2, 5, 1);
    run_view(
        "bidTreeValid",
        live_free_overlap,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut free_cycle = market.clone();
    write_free_order_slot(&mut free_cycle, 110, 4, 4);
    run_view(
        "bidTreeValid",
        free_cycle,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut wrong_live_count = market;
    write_allocator_header(&mut wrong_live_count, 110, 2, 2, 5, 4);
    run_view(
        "bidTreeValid",
        wrong_live_count,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn largest_bid_profile_validates_full_capacity_tree_with_fixed_memory() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        543_696,
        MARKET_HEADER_DISCRIMINANT,
        4096,
        4096,
        128,
    );
    write_allocator_header(&mut market, 110, 4095, 1, 4096, 4096);
    write_allocator_header(&mut market, 32882, 0, 0, 1, 1);
    write_allocator_header(&mut market, 65654, 0, 0, 1, 1);
    let mut rank = 0;
    write_perfect_bid_tree(&mut market, 110, 1, 4095, 0, &mut rank);
    assert_eq!(rank, 4095);
    run_view(
        "bidTreeValid",
        market,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
}

#[test]
fn ask_tree_uses_ascending_fifo_order_and_side_tag() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 0, 0, 1, 1);
    write_allocator_header(&mut market, 4210, 3, 2, 5, 4);
    write_allocator_header(&mut market, 8310, 0, 0, 1, 1);
    write_order_node(&mut market, 4210, 1, 0, 0, 2, 1, 90, 1);
    write_order_node(&mut market, 4210, 2, 1, 3, 0, 0, 100, 2);
    write_order_node(&mut market, 4210, 3, 0, 0, 2, 1, 110, 3);
    write_free_order_slot(&mut market, 4210, 4, 5);
    run_view(
        "askTreeValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let mut descending = market.clone();
    write_order_node(&mut descending, 4210, 1, 0, 0, 2, 1, 120, 1);
    run_view(
        "askTreeValid",
        descending,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut bid_side_sequence = market;
    write_order_node(&mut bid_side_sequence, 4210, 3, 0, 0, 2, 1, 110, !3u64);
    run_view(
        "askTreeValid",
        bid_side_sequence,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn largest_ask_profile_validates_full_capacity_tree_with_fixed_memory() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        543_696,
        MARKET_HEADER_DISCRIMINANT,
        4096,
        4096,
        128,
    );
    write_allocator_header(&mut market, 110, 0, 0, 1, 1);
    write_allocator_header(&mut market, 32882, 4095, 1, 4096, 4096);
    write_allocator_header(&mut market, 65654, 0, 0, 1, 1);
    let mut rank = 0;
    write_perfect_ask_tree(&mut market, 32882, 1, 4095, 0, &mut rank);
    assert_eq!(rank, 4095);
    run_view(
        "askTreeValid",
        market,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
}
