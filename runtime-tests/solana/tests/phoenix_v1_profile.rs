mod common;

use {
    mollusk_svm::result::Check,
    sokoban::{FromSlice, NodeAllocatorMap, RedBlackTree, ZeroCopy},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
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
const TRADER_TREE_WORD: usize = 8310;
type OfficialTraderTree = RedBlackTree<[u8; 32], [u64; 12], 128>;

fn key_words_bytes(key: [u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, word) in key.into_iter().enumerate() {
        bytes[index * 8..index * 8 + 8].copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

fn install_official_trader_tree(market: &mut Account, bytes: &[u8]) {
    let offset = 8 * TRADER_TREE_WORD;
    assert_eq!(bytes.len(), std::mem::size_of::<OfficialTraderTree>());
    assert_eq!(market.data.len() - offset, bytes.len());
    market.data[offset..].copy_from_slice(bytes);
}

fn assert_trader_tree_bytes_eq(actual: &[u8], expected: &[u8], step: usize) {
    assert_eq!(actual.len(), expected.len());
    if let Some(offset) = actual
        .iter()
        .zip(expected)
        .position(|(actual, expected)| actual != expected)
    {
        let word = offset / 8;
        let start = word * 8;
        let differences: Vec<_> = actual
            .iter()
            .zip(expected)
            .enumerate()
            .filter(|(_, (actual, expected))| actual != expected)
            .take(20)
            .collect();
        panic!(
            "Sokoban bytes diverged at step {step}: byte {offset}, word {word}, actual={:02x?}, expected={:02x?}; actual header={:02x?}, expected header={:02x?}; first differences={differences:?}",
            &actual[start..start + 8],
            &expected[start..start + 8],
            &actual[..32],
            &expected[..32],
        );
    }
}

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

fn read_word(account: &Account, word: usize) -> u64 {
    let offset = 8 * word;
    u64::from_le_bytes(account.data[offset..offset + 8].try_into().expect("word"))
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

fn write_trader_node(
    account: &mut Account,
    tree_root_word: usize,
    index: usize,
    left: u32,
    right: u32,
    parent: u32,
    color: u32,
    key: [u8; 32],
) {
    assert!(index > 0);
    let slot_word = tree_root_word + 4 + 18 * (index - 1);
    write_word(account, slot_word, packed_u32(left, right));
    write_word(account, slot_word + 1, packed_u32(parent, color));
    let key_offset = 8 * (slot_word + 2);
    account.data[key_offset..key_offset + 32].copy_from_slice(&key);
}

fn write_free_trader_slot(account: &mut Account, tree_root_word: usize, index: usize, next: u32) {
    assert!(index > 0);
    let slot_word = tree_root_word + 4 + 18 * (index - 1);
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

fn write_perfect_trader_tree(
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
        write_perfect_trader_tree(account, tree_root_word, left, last_index, index, rank);
    }
    *rank += 1;
    let mut key = [0u8; 32];
    key[24..32].copy_from_slice(&rank.to_be_bytes());
    write_trader_node(
        account,
        tree_root_word,
        index as usize,
        left.unwrap_or(0),
        right.unwrap_or(0),
        parent,
        0,
        key,
    );
    if let Some(right) = right {
        write_perfect_trader_tree(account, tree_root_word, right, last_index, index, rank);
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

fn run_market_write(
    name: &str,
    market: Account,
    writable: bool,
    args: &[u64],
    checks: &[Check],
) -> Account {
    let (program_id, mollusk) = common::harness_at(
        "PhoenixV1Profile",
        "PF_PHOENIX_V1_PROFILE_SO",
        PHOENIX_PROGRAM,
    );
    let state_key = common::dummy_state_key(&program_id);
    let market_key = Pubkey::new_unique();
    let market_meta = if writable {
        AccountMeta::new(market_key, false)
    } else {
        AccountMeta::new_readonly(market_key, false)
    };
    let instruction = common::instruction(
        program_id,
        state_key,
        name,
        args,
        true,
        false,
        vec![market_meta],
    );
    mollusk
        .process_and_validate_instruction(
            &instruction,
            &[
                (state_key, common::dummy_state_account(&program_id)),
                (market_key, market),
            ],
            checks,
        )
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &market_key)
        .expect("market after topology write")
        .1
}

fn run_topology_write(
    market: Account,
    writable: bool,
    slot: u64,
    links: u64,
    parent_color: u64,
    checks: &[Check],
) -> Account {
    run_market_write(
        "writeTraderTopology128",
        market,
        writable,
        &[slot, links, parent_color],
        checks,
    )
}

fn empty_small_market() -> Account {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 0, 0, 1, 1);
    write_allocator_header(&mut market, 4210, 0, 0, 1, 1);
    write_allocator_header(&mut market, 8310, 0, 0, 1, 1);
    market
}

fn market_with_first_trader(key: [u64; 4]) -> Account {
    run_market_write(
        "registerFirstTrader128",
        empty_small_market(),
        true,
        &key,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    )
}

fn market_with_two_traders(root_key: [u64; 4], child_key: [u64; 4]) -> Account {
    run_market_write(
        "registerSecondTrader128",
        market_with_first_trader(root_key),
        true,
        &child_key,
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    )
}

fn market_with_three_traders(
    first_key: [u64; 4],
    second_key: [u64; 4],
    third_key: [u64; 4],
) -> Account {
    run_market_write(
        "registerThirdTrader128",
        market_with_two_traders(first_key, second_key),
        true,
        &third_key,
        &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
    )
}

fn market_with_four_traders(
    first_key: [u64; 4],
    second_key: [u64; 4],
    third_key: [u64; 4],
    fourth_key: [u64; 4],
) -> Account {
    run_market_write(
        "registerFourthTrader128",
        market_with_three_traders(first_key, second_key, third_key),
        true,
        &fourth_key,
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    )
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
        let mut trader_left = [0u8; 32];
        trader_left[0] = 1;
        trader_left[1] = 255;
        let mut trader_root = [0u8; 32];
        trader_root[0] = 2;
        let mut trader_right = [0u8; 32];
        trader_right[0] = 3;
        write_word(&mut market, 106, 777);
        write_allocator_header(&mut market, 110, 1, 1, 2, 2);
        write_allocator_header(&mut market, ask_root_word, 2, 1, 3, 3);
        write_allocator_header(&mut market, trader_root_word, 3, 2, 4, 4);
        write_order_node(&mut market, 110, 1, 0, 0, 0, 0, 999, !1u64);
        write_order_node(&mut market, ask_root_word, 1, 0, 2, 0, 0, 100, 1);
        write_order_node(&mut market, ask_root_word, 2, 0, 0, 1, 1, 110, 2);
        write_trader_node(&mut market, trader_root_word, 1, 0, 0, 2, 1, trader_left);
        write_trader_node(&mut market, trader_root_word, 2, 1, 3, 0, 0, trader_root);
        write_trader_node(&mut market, trader_root_word, 3, 0, 0, 2, 1, trader_right);
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
            "traderTreeValid",
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

#[test]
fn trader_tree_uses_pubkey_byte_order_and_exact_allocator_partition() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    write_allocator_header(&mut market, 110, 0, 0, 1, 1);
    write_allocator_header(&mut market, 4210, 0, 0, 1, 1);
    write_allocator_header(&mut market, 8310, 3, 2, 5, 4);

    // Byte lexicographic order is left < root < right. Interpreting the first eight bytes as a
    // little-endian u64 would incorrectly place `left` after `root`.
    let mut left = [0u8; 32];
    left[0] = 1;
    left[1] = 255;
    let mut root = [0u8; 32];
    root[0] = 2;
    let mut right = [0u8; 32];
    right[0] = 3;
    write_trader_node(&mut market, 8310, 1, 0, 0, 2, 1, left);
    write_trader_node(&mut market, 8310, 2, 1, 3, 0, 0, root);
    write_trader_node(&mut market, 8310, 3, 0, 0, 2, 1, right);
    write_free_trader_slot(&mut market, 8310, 4, 5);
    run_view(
        "traderTreeValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let mut duplicate_key = market.clone();
    write_trader_node(&mut duplicate_key, 8310, 1, 0, 0, 2, 1, root);
    run_view(
        "traderTreeValid",
        duplicate_key,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut wrong_parent = market.clone();
    write_trader_node(&mut wrong_parent, 8310, 1, 0, 0, 3, 1, left);
    run_view(
        "traderTreeValid",
        wrong_parent,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut live_free_overlap = market.clone();
    write_allocator_header(&mut live_free_overlap, 8310, 3, 2, 5, 1);
    run_view(
        "traderTreeValid",
        live_free_overlap,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut free_cycle = market;
    write_free_trader_slot(&mut free_cycle, 8310, 4, 4);
    run_view(
        "traderTreeValid",
        free_cycle,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn largest_trader_profile_validates_8191_live_and_130_free_slots_with_fixed_memory() {
    let mut market = market_account(
        PHOENIX_PROGRAM,
        1_723_488,
        MARKET_HEADER_DISCRIMINANT,
        4096,
        4096,
        8321,
    );
    write_allocator_header(&mut market, 110, 0, 0, 1, 1);
    write_allocator_header(&mut market, 32882, 0, 0, 1, 1);
    write_allocator_header(&mut market, 65654, 8191, 1, 8322, 8192);
    let mut rank = 0;
    write_perfect_trader_tree(&mut market, 65654, 1, 8191, 0, &mut rank);
    assert_eq!(rank, 8191);
    for index in 8192..=8321 {
        write_free_trader_slot(&mut market, 65654, index, (index + 1) as u32);
    }
    run_view(
        "traderTreeValid",
        market,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
}

#[test]
fn trader_topology_write_is_fixed_capacity_owned_and_atomic() {
    const SLOT: u64 = 7;
    const LINKS: u64 = 0x0000_0009_0000_0003;
    const PARENT_COLOR: u64 = 0x0000_0001_0000_0005;
    let links_word = 8314 + 18 * SLOT as usize;
    let parent_color_word = links_word + 1;

    let market = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    let mut expected = market.clone();
    write_word(&mut expected, links_word, LINKS);
    write_word(&mut expected, parent_color_word, PARENT_COLOR);
    let written = run_topology_write(
        market,
        true,
        SLOT,
        LINKS,
        PARENT_COLOR,
        &[
            Check::success(),
            Check::return_data(&PARENT_COLOR.to_le_bytes()),
        ],
    );
    assert_eq!(written.data, expected.data);

    let readonly = expected.clone();
    let after_readonly = run_topology_write(
        readonly.clone(),
        false,
        SLOT,
        1,
        2,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, readonly.data);

    let wrong_owner = market_account(
        Pubkey::new_unique(),
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    let after_wrong_owner = run_topology_write(
        wrong_owner.clone(),
        true,
        SLOT,
        LINKS,
        PARENT_COLOR,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let bounded = expected.clone();
    let after_oob = run_topology_write(
        bounded.clone(),
        true,
        128,
        LINKS,
        PARENT_COLOR,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_oob.data, bounded.data);

    // The first word fits and the second does not. The failed instruction must roll back the first
    // store rather than exposing a partially updated persistent node.
    let short = market_account(
        PHOENIX_PROGRAM,
        (links_word + 1) * 8,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        128,
    );
    let after_short = run_topology_write(
        short.clone(),
        true,
        SLOT,
        LINKS,
        PARENT_COLOR,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_short.data, short.data);
}

#[test]
fn first_trader_registration_commits_a_complete_sokoban_root() {
    const KEY: [u64; 4] = [
        0x0706_0504_0302_0100,
        0x0f0e_0d0c_0b0a_0908,
        0x1716_1514_1312_1110,
        0x1f1e_1d1c_1b1a_1918,
    ];
    const CURSOR_1_1: u64 = 0x0000_0001_0000_0001;
    const CURSOR_2_2: u64 = 0x0000_0002_0000_0002;

    let mut fresh = empty_small_market();
    assert_eq!(read_word(&fresh, 8313), CURSOR_1_1);
    // A canonical fresh allocator obtains zeroed pages, but initialize the slot with stale bytes
    // to prove this entry point publishes a complete node rather than relying on heap-like reuse.
    for word in 8314..8332 {
        write_word(&mut fresh, word, u64::MAX);
    }

    let mut expected = fresh.clone();
    write_allocator_header(&mut expected, 8310, 1, 1, 2, 2);
    for word in 8314..8332 {
        write_word(&mut expected, word, 0);
    }
    for (offset, value) in KEY.into_iter().enumerate() {
        write_word(&mut expected, 8316 + offset, value);
    }
    let registered = run_market_write(
        "registerFirstTrader128",
        fresh.clone(),
        true,
        &KEY,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    assert_eq!(read_word(&registered, 8313), CURSOR_2_2);
    assert_eq!(registered.data, expected.data);
    run_view(
        "bodyEntryCount",
        registered.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    run_view(
        "traderTreeValid",
        registered.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let after_nonempty = run_market_write(
        "registerFirstTrader128",
        registered.clone(),
        true,
        &KEY,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_nonempty.data, registered.data);

    let after_readonly = run_market_write(
        "registerFirstTrader128",
        fresh.clone(),
        false,
        &KEY,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, fresh.data);

    let mut wrong_owner = fresh.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerFirstTrader128",
        wrong_owner.clone(),
        true,
        &KEY,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let malformed = market_account(
        PHOENIX_PROGRAM,
        SMALLEST_MARKET_BYTES,
        MARKET_HEADER_DISCRIMINANT,
        512,
        512,
        129,
    );
    let after_malformed = run_market_write(
        "registerFirstTrader128",
        malformed.clone(),
        true,
        &KEY,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn second_trader_registration_uses_pubkey_byte_order_and_complete_red_node() {
    // BYTE_SMALL is numerically greater as a little-endian u64, but its first raw byte is 0x00;
    // BYTE_LARGE starts with 0xff. This distinguishes Pubkey byte ordering from limb ordering.
    const BYTE_SMALL: [u64; 4] = [0x0100_0000_0000_0000, 1, 2, 3];
    const BYTE_LARGE: [u64; 4] = [0x0000_0000_0000_00ff, 1, 2, 3];
    const CURSOR_3_3: u64 = 0x0000_0003_0000_0003;
    const RED_CHILD_OF_ROOT: u64 = 0x0000_0001_0000_0001;

    let run_direction = |root_key: [u64; 4], key: [u64; 4], root_links: u64| {
        let mut one_root = market_with_first_trader(root_key);
        // Existing TraderState is not part of registration and must remain in place.
        write_word(&mut one_root, 8320, 77);
        // Prove that every byte in the newly bump-allocated slot is initialized before publish.
        for word in 8332..8350 {
            write_word(&mut one_root, word, u64::MAX);
        }

        let mut expected = one_root.clone();
        write_allocator_header(&mut expected, 8310, 2, 1, 3, 3);
        write_word(&mut expected, 8314, root_links);
        for word in 8332..8350 {
            write_word(&mut expected, word, 0);
        }
        write_word(&mut expected, 8333, RED_CHILD_OF_ROOT);
        for (offset, value) in key.into_iter().enumerate() {
            write_word(&mut expected, 8334 + offset, value);
        }

        let registered = run_market_write(
            "registerSecondTrader128",
            one_root,
            true,
            &key,
            &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
        );
        assert_eq!(read_word(&registered, 8313), CURSOR_3_3);
        assert_eq!(read_word(&registered, 8320), 77);
        assert_eq!(registered.data, expected.data);
        run_view(
            "bodyEntryCount",
            registered.clone(),
            &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
        );
        run_view(
            "traderTreeValid",
            registered.clone(),
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
        registered
    };

    let left_tree = run_direction(BYTE_LARGE, BYTE_SMALL, 2);
    let right_tree = run_direction(BYTE_SMALL, BYTE_LARGE, 2u64 << 32);

    let duplicate_start = market_with_first_trader(BYTE_SMALL);
    let after_duplicate = run_market_write(
        "registerSecondTrader128",
        duplicate_start.clone(),
        true,
        &BYTE_SMALL,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_duplicate.data, duplicate_start.data);

    let readonly_start = market_with_first_trader(BYTE_SMALL);
    let after_readonly = run_market_write(
        "registerSecondTrader128",
        readonly_start.clone(),
        false,
        &BYTE_LARGE,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, readonly_start.data);

    let mut wrong_owner = market_with_first_trader(BYTE_SMALL);
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerSecondTrader128",
        wrong_owner.clone(),
        true,
        &BYTE_LARGE,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = market_with_first_trader(BYTE_SMALL);
    write_word(&mut malformed, 8314, 9);
    let after_malformed = run_market_write(
        "registerSecondTrader128",
        malformed.clone(),
        true,
        &BYTE_LARGE,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);

    // Keep both directional outputs live through the end of the test.
    assert_eq!(read_word(&left_tree, 8314), 2);
    assert_eq!(read_word(&right_tree, 8314), 2u64 << 32);
}

#[test]
fn third_trader_registration_matches_all_sokoban_fixup_topologies() {
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];
    const CURSOR_4_4: u64 = 0x0000_0004_0000_0004;

    // (name, root key, existing child key, new key, final root, node topologies).
    // Each topology entry is (links, parent/color) for addresses 1, 2, and 3.
    let cases = [
        (
            "LL",
            C,
            B,
            A,
            2,
            [
                (0, packed_u32(2, 1)),
                (packed_u32(3, 1), 0),
                (0, packed_u32(2, 1)),
            ],
        ),
        (
            "LR",
            C,
            A,
            B,
            3,
            [
                (0, packed_u32(3, 1)),
                (0, packed_u32(3, 1)),
                (packed_u32(2, 1), 0),
            ],
        ),
        (
            "left child, new root-right",
            B,
            A,
            C,
            1,
            [
                (packed_u32(2, 3), 0),
                (0, packed_u32(1, 1)),
                (0, packed_u32(1, 1)),
            ],
        ),
        (
            "RR",
            A,
            B,
            C,
            2,
            [
                (0, packed_u32(2, 1)),
                (packed_u32(1, 3), 0),
                (0, packed_u32(2, 1)),
            ],
        ),
        (
            "RL",
            A,
            C,
            B,
            3,
            [
                (0, packed_u32(3, 1)),
                (0, packed_u32(3, 1)),
                (packed_u32(1, 2), 0),
            ],
        ),
        (
            "right child, new root-left",
            B,
            C,
            A,
            1,
            [
                (packed_u32(3, 2), 0),
                (0, packed_u32(1, 1)),
                (0, packed_u32(1, 1)),
            ],
        ),
    ];

    for (name, root_key, child_key, new_key, final_root, topology) in cases {
        let mut two_nodes = market_with_two_traders(root_key, child_key);
        // Existing TraderState belongs to the seats and must survive rotations unchanged.
        write_word(&mut two_nodes, 8320, 0x1111);
        write_word(&mut two_nodes, 8338, 0x2222);
        // Address 3 is bump-allocated. Stale bytes prove the complete 144-byte slot is replaced.
        for word in 8350..8368 {
            write_word(&mut two_nodes, word, u64::MAX);
        }

        let mut expected = two_nodes.clone();
        write_allocator_header(&mut expected, 8310, 3, final_root, 4, 4);
        for word in 8350..8368 {
            write_word(&mut expected, word, 0);
        }
        for (offset, value) in new_key.into_iter().enumerate() {
            write_word(&mut expected, 8352 + offset, value);
        }
        for (index, (links, parent_color)) in topology.into_iter().enumerate() {
            let slot_word = 8314 + 18 * index;
            write_word(&mut expected, slot_word, links);
            write_word(&mut expected, slot_word + 1, parent_color);
        }

        let registered = run_market_write(
            "registerThirdTrader128",
            two_nodes,
            true,
            &new_key,
            &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
        );
        assert_eq!(read_word(&registered, 8313), CURSOR_4_4, "{name}");
        assert_eq!(read_word(&registered, 8320), 0x1111, "{name}");
        assert_eq!(read_word(&registered, 8338), 0x2222, "{name}");
        assert_eq!(registered.data, expected.data, "{name}");
        run_view(
            "bodyEntryCount",
            registered.clone(),
            &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
        );
        run_view(
            "traderTreeValid",
            registered,
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
    }
}

#[test]
fn third_trader_registration_rejects_noncanonical_inputs_atomically() {
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];

    let canonical = market_with_two_traders(A, B);
    for duplicate in [A, B] {
        let after_duplicate = run_market_write(
            "registerThirdTrader128",
            canonical.clone(),
            true,
            &duplicate,
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(after_duplicate.data, canonical.data);
    }

    let after_readonly = run_market_write(
        "registerThirdTrader128",
        canonical.clone(),
        false,
        &C,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerThirdTrader128",
        wrong_owner.clone(),
        true,
        &C,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = canonical;
    write_word(&mut malformed, 8314, 9);
    let after_malformed = run_market_write(
        "registerThirdTrader128",
        malformed.clone(),
        true,
        &C,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn fourth_trader_registration_handles_every_three_node_address_layout() {
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];
    const LOW: [u64; 4] = [0x05, 0, 0, 0];
    const LEFT_INNER: [u64; 4] = [0x18, 0, 0, 0];
    const RIGHT_INNER: [u64; 4] = [0x28, 0, 0, 0];
    const HIGH: [u64; 4] = [0x40, 0, 0, 0];
    const CURSOR_5_5: u64 = 0x0000_0005_0000_0005;

    // The first three keys produce all six possible address assignments for the same canonical
    // black-root/two-red-leaf shape. The fourth key covers all four child-link positions.
    let cases = [
        ("LL layout, outer left", C, B, A, LOW, 2, 3, 1, 3, 4),
        (
            "LR layout, inner left",
            C,
            A,
            B,
            LEFT_INNER,
            3,
            2,
            1,
            2,
            4u64 << 32,
        ),
        (
            "no-fix layout, inner right",
            B,
            A,
            C,
            RIGHT_INNER,
            1,
            2,
            3,
            3,
            4,
        ),
        (
            "RR layout, outer right",
            A,
            B,
            C,
            HIGH,
            2,
            1,
            3,
            3,
            4u64 << 32,
        ),
        ("RL address layout", A, C, B, LOW, 3, 1, 2, 1, 4),
        (
            "opposite no-fix address layout",
            B,
            C,
            A,
            HIGH,
            1,
            3,
            2,
            2,
            4u64 << 32,
        ),
    ];

    for (name, first, second, third, fourth, root, left, right, parent, parent_links) in cases {
        let mut three_nodes = market_with_three_traders(first, second, third);
        for (word, value) in [(8320, 0x1111), (8338, 0x2222), (8356, 0x3333)] {
            write_word(&mut three_nodes, word, value);
        }
        for word in 8368..8386 {
            write_word(&mut three_nodes, word, u64::MAX);
        }

        let mut expected = three_nodes.clone();
        write_allocator_header(&mut expected, 8310, 4, root, 5, 5);
        for word in 8368..8386 {
            write_word(&mut expected, word, 0);
        }
        write_word(&mut expected, 8369, packed_u32(parent, 1));
        for (offset, value) in fourth.into_iter().enumerate() {
            write_word(&mut expected, 8370 + offset, value);
        }
        let parent_slot = 8314 + 18 * (parent as usize - 1);
        write_word(&mut expected, parent_slot, parent_links);
        for child in [left, right] {
            let child_slot = 8314 + 18 * (child as usize - 1);
            write_word(&mut expected, child_slot + 1, u64::from(root));
        }

        let registered = run_market_write(
            "registerFourthTrader128",
            three_nodes,
            true,
            &fourth,
            &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
        );
        assert_eq!(read_word(&registered, 8313), CURSOR_5_5, "{name}");
        assert_eq!(read_word(&registered, 8320), 0x1111, "{name}");
        assert_eq!(read_word(&registered, 8338), 0x2222, "{name}");
        assert_eq!(read_word(&registered, 8356), 0x3333, "{name}");
        assert_eq!(registered.data, expected.data, "{name}");
        run_view(
            "bodyEntryCount",
            registered.clone(),
            &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
        );
        run_view(
            "traderTreeValid",
            registered,
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
    }
}

#[test]
fn fourth_trader_registration_rejects_noncanonical_inputs_atomically() {
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];
    const D: [u64; 4] = [0x40, 0, 0, 0];

    let canonical = market_with_three_traders(A, B, C);
    for duplicate in [A, B, C] {
        let after_duplicate = run_market_write(
            "registerFourthTrader128",
            canonical.clone(),
            true,
            &duplicate,
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(after_duplicate.data, canonical.data);
    }

    let after_readonly = run_market_write(
        "registerFourthTrader128",
        canonical.clone(),
        false,
        &D,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerFourthTrader128",
        wrong_owner.clone(),
        true,
        &D,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = canonical;
    write_word(&mut malformed, 8315, 0);
    let after_malformed = run_market_write(
        "registerFourthTrader128",
        malformed.clone(),
        true,
        &D,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn fifth_trader_registration_matches_black_parent_and_all_black_uncle_fixups() {
    const K02: [u64; 4] = [0x02, 0, 0, 0];
    const K05: [u64; 4] = [0x05, 0, 0, 0];
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const K14: [u64; 4] = [0x14, 0, 0, 0];
    const K18: [u64; 4] = [0x18, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const K28: [u64; 4] = [0x28, 0, 0, 0];
    const K2C: [u64; 4] = [0x2c, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];
    const K40: [u64; 4] = [0x40, 0, 0, 0];
    const K50: [u64; 4] = [0x50, 0, 0, 0];
    const CURSOR_6_6: u64 = 0x0000_0006_0000_0006;

    // Each case starts from the official first-through-fourth bump path. Together they cover all
    // six address layouts, LL/LR/RL/RR black-uncle repair, and black-parent insertion both beside
    // the red leaf's grandparent and below the opposite black sibling.
    let cases = [
        (
            "LL below red address 4",
            [C, B, A, K05, K02],
            2,
            [
                (0, packed_u32(2, 0)),
                (packed_u32(4, 1), 0),
                (0, packed_u32(4, 1)),
                (packed_u32(5, 3), packed_u32(2, 0)),
                (0, packed_u32(4, 1)),
            ],
        ),
        (
            "RL below red address 4",
            [C, A, B, K18, K14],
            3,
            [
                (0, packed_u32(3, 0)),
                (0, packed_u32(5, 1)),
                (packed_u32(5, 1), 0),
                (0, packed_u32(5, 1)),
                (packed_u32(2, 4), packed_u32(3, 0)),
            ],
        ),
        (
            "LR below red address 4",
            [B, A, C, K28, K2C],
            1,
            [
                (packed_u32(2, 5), 0),
                (0, packed_u32(1, 0)),
                (0, packed_u32(5, 1)),
                (0, packed_u32(5, 1)),
                (packed_u32(4, 3), packed_u32(1, 0)),
            ],
        ),
        (
            "RR below red address 4",
            [A, B, C, K40, K50],
            2,
            [
                (0, packed_u32(2, 0)),
                (packed_u32(1, 4), 0),
                (0, packed_u32(4, 1)),
                (packed_u32(3, 5), packed_u32(2, 0)),
                (0, packed_u32(4, 1)),
            ],
        ),
        (
            "black grandparent missing right",
            [A, C, B, K05, K18],
            3,
            [
                (packed_u32(4, 5), packed_u32(3, 0)),
                (0, packed_u32(3, 0)),
                (packed_u32(1, 2), 0),
                (0, packed_u32(1, 1)),
                (0, packed_u32(1, 1)),
            ],
        ),
        (
            "black grandparent missing left",
            [B, C, A, K40, K28],
            1,
            [
                (packed_u32(3, 2), 0),
                (packed_u32(5, 4), packed_u32(1, 0)),
                (0, packed_u32(1, 0)),
                (0, packed_u32(2, 1)),
                (0, packed_u32(2, 1)),
            ],
        ),
        (
            "opposite black sibling missing left",
            [C, B, A, K05, K28],
            2,
            [
                (packed_u32(5, 0), packed_u32(2, 0)),
                (packed_u32(3, 1), 0),
                (packed_u32(4, 0), packed_u32(2, 0)),
                (0, packed_u32(3, 1)),
                (0, packed_u32(1, 1)),
            ],
        ),
        (
            "opposite black sibling missing right",
            [A, B, C, K40, K18],
            2,
            [
                (packed_u32(0, 5), packed_u32(2, 0)),
                (packed_u32(1, 3), 0),
                (packed_u32(0, 4), packed_u32(2, 0)),
                (0, packed_u32(3, 1)),
                (0, packed_u32(1, 1)),
            ],
        ),
    ];

    for (name, keys, final_root, topology) in cases {
        let mut four_nodes = market_with_four_traders(keys[0], keys[1], keys[2], keys[3]);
        for (address, value) in [0x1111, 0x2222, 0x3333, 0x4444].into_iter().enumerate() {
            write_word(&mut four_nodes, 8320 + 18 * address, value);
        }
        for word in 8386..8404 {
            write_word(&mut four_nodes, word, u64::MAX);
        }

        let mut expected = four_nodes.clone();
        write_allocator_header(&mut expected, 8310, 5, final_root, 6, 6);
        for word in 8386..8404 {
            write_word(&mut expected, word, 0);
        }
        for (offset, value) in keys[4].into_iter().enumerate() {
            write_word(&mut expected, 8388 + offset, value);
        }
        for (index, (links, parent_color)) in topology.into_iter().enumerate() {
            write_word(&mut expected, 8314 + 18 * index, links);
            write_word(&mut expected, 8315 + 18 * index, parent_color);
        }

        let registered = run_market_write(
            "registerFifthTrader128",
            four_nodes,
            true,
            &keys[4],
            &[Check::success(), Check::return_data(&5u64.to_le_bytes())],
        );
        assert_eq!(read_word(&registered, 8313), CURSOR_6_6, "{name}");
        for (address, value) in [0x1111, 0x2222, 0x3333, 0x4444].into_iter().enumerate() {
            assert_eq!(read_word(&registered, 8320 + 18 * address), value, "{name}");
        }
        assert_eq!(registered.data, expected.data, "{name}");
        run_view(
            "bodyEntryCount",
            registered.clone(),
            &[Check::success(), Check::return_data(&5u64.to_le_bytes())],
        );
        run_view(
            "traderTreeValid",
            registered,
            &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
        );
    }
}

#[test]
fn fifth_trader_registration_rejects_noncanonical_inputs_atomically() {
    const A: [u64; 4] = [0x10, 0, 0, 0];
    const B: [u64; 4] = [0x20, 0, 0, 0];
    const C: [u64; 4] = [0x30, 0, 0, 0];
    const D: [u64; 4] = [0x40, 0, 0, 0];
    const E: [u64; 4] = [0x50, 0, 0, 0];

    let canonical = market_with_four_traders(A, B, C, D);
    for duplicate in [A, B, C, D] {
        let after_duplicate = run_market_write(
            "registerFifthTrader128",
            canonical.clone(),
            true,
            &duplicate,
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(after_duplicate.data, canonical.data);
    }

    let after_readonly = run_market_write(
        "registerFifthTrader128",
        canonical.clone(),
        false,
        &E,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerFifthTrader128",
        wrong_owner.clone(),
        true,
        &E,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = canonical;
    write_word(&mut malformed, 8369, 3);
    let after_malformed = run_market_write(
        "registerFifthTrader128",
        malformed.clone(),
        true,
        &E,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn generic_trader_registration_matches_sokoban_through_capacity() {
    assert_eq!(std::mem::size_of::<OfficialTraderTree>(), 18_464);
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let mut market = empty_small_market();

    // Multiplication by an odd number permutes all 128 first-byte values. This exercises general
    // recursive red-uncle repair and both rotation directions rather than an insertion-count case.
    let keys: Vec<[u64; 4]> = (0u64..128)
        .map(|index| [(index * 73) % 128, 0, 0, 0])
        .collect();
    for (index, key) in keys.iter().copied().enumerate() {
        {
            let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official tree bytes");
            assert_eq!(
                official.insert(key_words_bytes(key), [0; 12]),
                Some(index as u32 + 1)
            );
            assert!(official.is_valid_red_black_tree());
        }
        market = run_market_write(
            "registerTrader128",
            market,
            true,
            &key,
            &[
                Check::success(),
                Check::return_data(&((index as u64) + 1).to_le_bytes()),
            ],
        );
        assert_trader_tree_bytes_eq(
            &market.data[8 * TRADER_TREE_WORD..],
            official_bytes.as_slice(),
            index + 1,
        );
    }

    run_view(
        "traderTreeValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    let before_full = market.clone();
    let after_full = run_market_write(
        "registerTrader128",
        market.clone(),
        true,
        &[128, 0, 0, 0],
        &[Check::err(ProgramError::Custom(0x1003))],
    );
    assert_eq!(after_full.data, before_full.data);

    // Duplicate detection precedes the capacity check and never applies Sokoban's map-style
    // replacement behavior to a registered TraderState.
    let after_duplicate = run_market_write(
        "registerTrader128",
        market.clone(),
        true,
        &keys[37],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_duplicate.data, market.data);
}

#[test]
fn generic_trader_registration_reuses_free_head_and_fails_atomically() {
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let keys: Vec<[u64; 4]> = (0u64..24)
        .map(|index| [((index * 17) % 29) + 1, 0, 0, 0])
        .collect();
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        for (index, key) in keys.iter().copied().enumerate() {
            let mut state = [0u64; 12];
            state[0] = 0x1000 + index as u64;
            assert!(official.insert(key_words_bytes(key), state).is_some());
        }
        assert!(official.remove(&key_words_bytes(keys[7])).is_some());
        assert!(official.is_valid_red_black_tree());
    }
    let mut market = empty_small_market();
    install_official_trader_tree(&mut market, &official_bytes);
    let before_reuse = market.clone();
    let replacement = [0xfe, 0, 0, 0];
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        assert!(official
            .insert(key_words_bytes(replacement), [0; 12])
            .is_some());
        assert!(official.is_valid_red_black_tree());
    }
    let reused = run_market_write(
        "registerTrader128",
        market,
        true,
        &replacement,
        &[Check::success(), Check::return_data(&24u64.to_le_bytes())],
    );
    assert_trader_tree_bytes_eq(
        &reused.data[8 * TRADER_TREE_WORD..],
        official_bytes.as_slice(),
        24,
    );
    // Free-list reuse leaves the bump boundary unchanged while consuming the free head.
    assert_eq!(
        read_word(&reused, 8313) & 0xffff_ffff,
        read_word(&before_reuse, 8313) & 0xffff_ffff
    );

    let readonly = run_market_write(
        "registerTrader128",
        reused.clone(),
        false,
        &[0xff, 0, 0, 0],
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(readonly.data, reused.data);

    let mut wrong_owner = reused.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "registerTrader128",
        wrong_owner.clone(),
        true,
        &[0xff, 0, 0, 0],
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = reused;
    write_word(&mut malformed, 8315, 7);
    let after_malformed = run_market_write(
        "registerTrader128",
        malformed.clone(),
        true,
        &[0xff, 0, 0, 0],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn generic_trader_removal_matches_sokoban_through_empty_and_reuse() {
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let keys: Vec<[u64; 4]> = (0u64..128)
        .map(|index| [(index * 73) % 128, 0, 0, 0])
        .collect();
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        for (index, key) in keys.iter().copied().enumerate() {
            let mut state = [0u64; 12];
            state[0] = 0x1000 + index as u64;
            state[11] = 0xf000 + index as u64;
            assert!(official.insert(key_words_bytes(key), state).is_some());
        }
        assert!(official.is_valid_red_black_tree());
    }
    let mut market = empty_small_market();
    install_official_trader_tree(&mut market, &official_bytes);

    // Multiplication by another odd number permutes the 128 insertion positions. Removing this
    // order exercises leaf/one-child/two-child predecessor transplants and every delete-fixup arm.
    for step in 0..128 {
        let key = keys[(step * 53) % 128];
        {
            let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official tree bytes");
            assert!(official.remove(&key_words_bytes(key)).is_some());
            assert!(official.is_valid_red_black_tree());
        }
        let remaining = 127 - step;
        market = run_market_write(
            "removeTrader128",
            market,
            true,
            &key,
            &[
                Check::success(),
                Check::return_data(&(remaining as u64).to_le_bytes()),
            ],
        );
        assert_trader_tree_bytes_eq(
            &market.data[8 * TRADER_TREE_WORD..],
            official_bytes.as_slice(),
            step + 1,
        );
    }
    run_view(
        "traderTreeValid",
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let empty = market.clone();
    let missing = run_market_write(
        "removeTrader128",
        market.clone(),
        true,
        &keys[0],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(missing.data, empty.data);

    // Reinsert into the official deletion free-list and require exact LIFO address reuse. A reused
    // slot is fully reinitialized by insertion even though deletion leaves key/value bytes in place.
    for index in 0u64..16 {
        let key = [0x80 + index, 1, 0, 0];
        {
            let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official tree bytes");
            assert!(official.insert(key_words_bytes(key), [0; 12]).is_some());
            assert!(official.is_valid_red_black_tree());
        }
        market = run_market_write(
            "registerTrader128",
            market,
            true,
            &key,
            &[
                Check::success(),
                Check::return_data(&(index + 1).to_le_bytes()),
            ],
        );
        assert_trader_tree_bytes_eq(
            &market.data[8 * TRADER_TREE_WORD..],
            official_bytes.as_slice(),
            129 + index as usize,
        );
    }
}

#[test]
fn generic_trader_removal_rejects_missing_and_noncanonical_inputs_atomically() {
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let keys: Vec<[u64; 4]> = (1u64..=31).map(|index| [index * 7, 0, 0, 0]).collect();
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        for key in keys.iter().copied() {
            assert!(official.insert(key_words_bytes(key), [0; 12]).is_some());
        }
    }
    let mut canonical = empty_small_market();
    install_official_trader_tree(&mut canonical, &official_bytes);

    let absent = [0xff, 0, 0, 0];
    let after_absent = run_market_write(
        "removeTrader128",
        canonical.clone(),
        true,
        &absent,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_absent.data, canonical.data);

    let after_readonly = run_market_write(
        "removeTrader128",
        canonical.clone(),
        false,
        &keys[12],
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "removeTrader128",
        wrong_owner.clone(),
        true,
        &keys[12],
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = canonical;
    write_word(&mut malformed, 8315, 127);
    let after_malformed = run_market_write(
        "removeTrader128",
        malformed.clone(),
        true,
        &keys[12],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}
