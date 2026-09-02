mod common;

use {
    base64::{engine::general_purpose::STANDARD as BASE64, Engine as _},
    bytemuck::{Pod, Zeroable},
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sokoban::{FromSlice, NodeAllocatorMap, RedBlackTree, ZeroCopy},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_svm_log_collector::LogCollector,
    spl_token_interface::state::{Account as TokenAccount, AccountState},
};

const MARKET_HEADER_DISCRIMINANT: u64 = 8_167_313_896_524_341_111;
const SEAT_DISCRIMINANT: u64 = 2_002_603_505_298_356_104;
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
const MARKET_SEQUENCE_WORD: usize = 34;
const ORDER_SEQUENCE_WORD: usize = 106;
const BID_TREE_WORD: usize = 110;
const ASK_TREE_WORD: usize = 4210;
const TRADER_TREE_WORD: usize = 8310;
type OfficialTraderTree = RedBlackTree<[u8; 32], [u64; 12], 128>;

#[repr(C)]
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Pod, Zeroable)]
struct OfficialOrderId {
    price_in_ticks: u64,
    order_sequence_number: u64,
}

impl PartialOrd for OfficialOrderId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let (price, sequence) = if self.order_sequence_number >> 63 == 1 {
            (
                other.price_in_ticks.cmp(&self.price_in_ticks),
                other.order_sequence_number.cmp(&self.order_sequence_number),
            )
        } else {
            (
                self.price_in_ticks.cmp(&other.price_in_ticks),
                self.order_sequence_number.cmp(&other.order_sequence_number),
            )
        };
        Some(if price == std::cmp::Ordering::Equal {
            sequence
        } else {
            price
        })
    }
}

impl Ord for OfficialOrderId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).expect("total FIFO order")
    }
}

type OfficialOrderTree = RedBlackTree<OfficialOrderId, [u64; 4], 512>;

fn key_words_bytes(key: [u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, word) in key.into_iter().enumerate() {
        bytes[index * 8..index * 8 + 8].copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

fn pubkey_words(key: Pubkey) -> [u64; 4] {
    let bytes = key.to_bytes();
    std::array::from_fn(|index| {
        u64::from_le_bytes(
            bytes[index * 8..index * 8 + 8]
                .try_into()
                .expect("pubkey word"),
        )
    })
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

fn install_official_order_tree(market: &mut Account, tree_word: usize, bytes: &[u8]) {
    let offset = 8 * tree_word;
    assert_eq!(bytes.len(), std::mem::size_of::<OfficialOrderTree>());
    market.data[offset..offset + bytes.len()].copy_from_slice(bytes);
}

fn assert_order_tree_bytes_eq(
    market: &Account,
    tree_word: usize,
    expected: &[u8],
    side: &str,
    step: usize,
) {
    let offset = 8 * tree_word;
    let actual = &market.data[offset..offset + expected.len()];
    if let Some(byte) = actual
        .iter()
        .zip(expected)
        .position(|(actual, expected)| actual != expected)
    {
        let word = byte / 8;
        panic!(
            "{side} Sokoban bytes diverged at step {step}: byte {byte}, word {word}, actual={:02x?}, expected={:02x?}",
            &actual[word * 8..word * 8 + 8],
            &expected[word * 8..word * 8 + 8],
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

fn write_pubkey(account: &mut Account, offset: usize, value: Pubkey) {
    account.data[offset..offset + 32].copy_from_slice(value.as_ref());
}

fn read_word(account: &Account, word: usize) -> u64 {
    let offset = 8 * word;
    u64::from_le_bytes(account.data[offset..offset + 8].try_into().expect("word"))
}

fn packed_u32(low: u32, high: u32) -> u64 {
    u64::from(low) | (u64::from(high) << 32)
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

fn token_amount(account: &Account) -> u64 {
    u64::from_le_bytes(
        account.data[64..72]
            .try_into()
            .expect("SPL Token account amount"),
    )
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
    write_word(&mut market, ORDER_SEQUENCE_WORD, 1);
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

fn market_with_signer_trader() -> Account {
    let trader = pubkey_words(common::dummy_state_key(&PHOENIX_PROGRAM));
    let mut args = trader.to_vec();
    args.extend([0, 0]);
    let mut market = run_market_write(
        "depositTrader128",
        empty_small_market(),
        true,
        &args,
        &[Check::success()],
    );
    write_word(&mut market, 1, 1);
    market
}

fn raw_place_data(
    side: u8,
    price: u64,
    base_lots: u64,
    client_id_low: u64,
    client_id_high: u64,
) -> Vec<u8> {
    let mut data = vec![3, 0, side];
    data.extend_from_slice(&price.to_le_bytes());
    data.extend_from_slice(&base_lots.to_le_bytes());
    data.extend_from_slice(&client_id_low.to_le_bytes());
    data.extend_from_slice(&client_id_high.to_le_bytes());
    // reject_post_only=false, use_only_deposited_funds=true, no TIF, and hard funds failure.
    data.extend_from_slice(&[0, 1, 0, 0, 0]);
    assert_eq!(data.len(), 40);
    data
}

fn raw_limit_data(
    side: u8,
    price: u64,
    base_lots: u64,
    client_id_low: u64,
    client_id_high: u64,
) -> Vec<u8> {
    raw_limit_data_with_match_limit(side, price, base_lots, 1, client_id_low, client_id_high)
}

fn raw_limit_data_with_match_limit(
    side: u8,
    price: u64,
    base_lots: u64,
    match_limit: u64,
    client_id_low: u64,
    client_id_high: u64,
) -> Vec<u8> {
    let mut data = vec![3, 1, side];
    data.extend_from_slice(&price.to_le_bytes());
    data.extend_from_slice(&base_lots.to_le_bytes());
    // SelfTradeBehavior::Abort and a present bounded match limit.
    data.extend_from_slice(&[0, 1]);
    data.extend_from_slice(&match_limit.to_le_bytes());
    data.extend_from_slice(&client_id_low.to_le_bytes());
    data.extend_from_slice(&client_id_high.to_le_bytes());
    // Deposited funds only, no TIF, and hard insufficient-funds failure.
    data.extend_from_slice(&[1, 0, 0, 0]);
    assert_eq!(data.len(), 49);
    data
}

fn place_return_data(price: u64, encoded_sequence: u64) -> Vec<u8> {
    // Official Phoenix sets Borsh `Vec<FIFOOrderId>` return data after event CPIs.
    let mut data = 1u32.to_le_bytes().to_vec();
    data.extend_from_slice(&price.to_le_bytes());
    data.extend_from_slice(&encoded_sequence.to_le_bytes());
    assert_eq!(data.len(), 20);
    data
}

fn raw_reduce_data(side: u8, price: u64, sequence: u64, size: u64) -> Vec<u8> {
    raw_reduce_data_for_tag(5, side, price, sequence, size)
}

fn raw_reduce_withdraw_data(side: u8, price: u64, sequence: u64, size: u64) -> Vec<u8> {
    raw_reduce_data_for_tag(4, side, price, sequence, size)
}

fn raw_cancel_all_data(tag: u8) -> Vec<u8> {
    assert!(tag == 6 || tag == 7);
    vec![tag]
}

fn raw_cancel_up_to_data(
    tag: u8,
    side: u8,
    tick_limit: Option<u64>,
    search_limit: Option<u32>,
    cancel_limit: Option<u32>,
) -> Vec<u8> {
    assert!(tag == 8 || tag == 9);
    let mut data = vec![tag, side];
    match tick_limit {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    for limit in [search_limit, cancel_limit] {
        match limit {
            Some(value) => {
                data.push(1);
                data.extend_from_slice(&value.to_le_bytes());
            }
            None => data.push(0),
        }
    }
    assert!((5..=21).contains(&data.len()));
    data
}

/// Official Borsh `CancelMultipleOrdersByIdParams`: `tag || u32 len || CancelOrderParams*`.
/// This profile slice accepts at most eight ids (`len ∈ {0..=8}`; max wire 141 bytes).
/// Tag 10 withdraw accepts at most eight ids (`len ∈ {0..=8}`; max wire 141 bytes).
fn raw_cancel_by_id_data(tag: u8, orders: &[(u8, u64, u64)]) -> Vec<u8> {
    assert!(tag == 10 || tag == 11);
    assert!(orders.len() <= 8);
    let mut data = vec![tag];
    data.extend_from_slice(&(orders.len() as u32).to_le_bytes());
    for &(side, price, sequence) in orders {
        data.push(side);
        data.extend_from_slice(&price.to_le_bytes());
        data.extend_from_slice(&sequence.to_le_bytes());
    }
    assert!((5..=141).contains(&data.len()));
    data
}

fn raw_withdraw_funds_data(quote_lots: Option<u64>, base_lots: Option<u64>) -> Vec<u8> {
    let mut data = vec![12];
    match quote_lots {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    match base_lots {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    assert!((3..=19).contains(&data.len()));
    data
}

fn raw_deposit_funds_data(quote_lots: Option<u64>, base_lots: Option<u64>) -> Vec<u8> {
    let mut data = vec![13];
    match quote_lots {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    match base_lots {
        Some(value) => {
            data.push(1);
            data.extend_from_slice(&value.to_le_bytes());
        }
        None => data.push(0),
    }
    assert!((3..=19).contains(&data.len()));
    data
}

fn raw_reduce_data_for_tag(tag: u8, side: u8, price: u64, sequence: u64, size: u64) -> Vec<u8> {
    let mut data = vec![tag, side];
    data.extend_from_slice(&price.to_le_bytes());
    data.extend_from_slice(&sequence.to_le_bytes());
    data.extend_from_slice(&size.to_le_bytes());
    assert_eq!(data.len(), 26);
    data
}

fn raw_reduce_instruction(
    data: &[u8],
    program_account: Pubkey,
    log_key: Pubkey,
    log_writable: bool,
    market_key: Pubkey,
    market_writable: bool,
    trader_key: Pubkey,
    trader_signer: bool,
    trader_writable: bool,
) -> Instruction {
    let log_meta = if log_writable {
        AccountMeta::new(log_key, false)
    } else {
        AccountMeta::new_readonly(log_key, false)
    };
    let market_meta = if market_writable {
        AccountMeta::new(market_key, false)
    } else {
        AccountMeta::new_readonly(market_key, false)
    };
    let trader_meta = if trader_writable {
        AccountMeta::new(trader_key, trader_signer)
    } else {
        AccountMeta::new_readonly(trader_key, trader_signer)
    };
    Instruction::new_with_bytes(
        PHOENIX_PROGRAM,
        data,
        vec![
            AccountMeta::new_readonly(program_account, false),
            log_meta,
            market_meta,
            trader_meta,
        ],
    )
}

fn seat_account(market_key: Pubkey, trader_key: Pubkey) -> Account {
    let mut seat = Account::new(1, 128, &PHOENIX_PROGRAM);
    write_word(&mut seat, 0, SEAT_DISCRIMINANT);
    write_pubkey(&mut seat, 8, market_key);
    write_pubkey(&mut seat, 40, trader_key);
    write_word(&mut seat, 9, 1);
    seat
}

fn raw_place_instruction(
    data: &[u8],
    program_account: Pubkey,
    log_key: Pubkey,
    market_key: Pubkey,
    market_writable: bool,
    trader_key: Pubkey,
    trader_signer: bool,
    seat_key: Pubkey,
) -> Instruction {
    let market_meta = if market_writable {
        AccountMeta::new(market_key, false)
    } else {
        AccountMeta::new_readonly(market_key, false)
    };
    Instruction::new_with_bytes(
        PHOENIX_PROGRAM,
        data,
        vec![
            AccountMeta::new_readonly(program_account, false),
            AccountMeta::new_readonly(log_key, false),
            market_meta,
            AccountMeta::new_readonly(trader_key, trader_signer),
            AccountMeta::new_readonly(seat_key, false),
        ],
    )
}

fn raw_place_accounts(
    program_account: Pubkey,
    log_key: Pubkey,
    market_key: Pubkey,
    market: Account,
    trader_key: Pubkey,
    seat_key: Pubkey,
    seat: Account,
) -> Vec<(Pubkey, Account)> {
    vec![
        (
            program_account,
            mollusk_svm::program::create_program_account_loader_v3(&program_account),
        ),
        (log_key, common::plain_account()),
        (market_key, market),
        (trader_key, common::plain_account()),
        (seat_key, seat),
    ]
}

fn raw_reduce_harness() -> (Mollusk, Pubkey) {
    let (_, mut mollusk) = common::harness_at(
        "PhoenixV1Profile",
        "PF_PHOENIX_V1_PROFILE_SO",
        PHOENIX_PROGRAM,
    );
    mollusk.logger = Some(LogCollector::new_ref_with_limit(None));
    token::add_program(&mut mollusk);
    let (log_key, _) = Pubkey::find_program_address(&[b"log"], &PHOENIX_PROGRAM);
    (mollusk, log_key)
}

fn raw_reduce_accounts(
    program_account: Pubkey,
    log_key: Pubkey,
    market_key: Pubkey,
    market: Account,
    trader_key: Pubkey,
) -> Vec<(Pubkey, Account)> {
    vec![
        (
            program_account,
            mollusk_svm::program::create_program_account_loader_v3(&program_account),
        ),
        (log_key, common::plain_account()),
        (market_key, market),
        (trader_key, common::plain_account()),
    ]
}

#[derive(Clone)]
struct RawReduceTokenFixture {
    log_key: Pubkey,
    market_key: Pubkey,
    market: Account,
    trader_key: Pubkey,
    trader_base_key: Pubkey,
    trader_base: Account,
    trader_quote_key: Pubkey,
    trader_quote: Account,
    base_mint_key: Pubkey,
    base_vault_key: Pubkey,
    base_vault: Account,
    quote_vault_key: Pubkey,
    quote_vault: Account,
    token_program_key: Pubkey,
    token_program: Account,
}

impl RawReduceTokenFixture {
    fn new(market_key: Pubkey, trader_key: Pubkey, mut market: Account) -> Self {
        let (log_key, _) = Pubkey::find_program_address(&[b"log"], &PHOENIX_PROGRAM);
        let base_mint_key = Pubkey::new_unique();
        let quote_mint_key = Pubkey::new_unique();
        let (base_vault_key, base_bump) = Pubkey::find_program_address(
            &[b"vault", market_key.as_ref(), base_mint_key.as_ref()],
            &PHOENIX_PROGRAM,
        );
        let (quote_vault_key, quote_bump) = Pubkey::find_program_address(
            &[b"vault", market_key.as_ref(), quote_mint_key.as_ref()],
            &PHOENIX_PROGRAM,
        );
        write_word(&mut market, 5, packed_u32(6, u32::from(base_bump)));
        write_pubkey(&mut market, 48, base_mint_key);
        write_pubkey(&mut market, 80, base_vault_key);
        write_word(&mut market, 14, 2);
        write_word(&mut market, 15, packed_u32(6, u32::from(quote_bump)));
        write_pubkey(&mut market, 128, quote_mint_key);
        write_pubkey(&mut market, 160, quote_vault_key);
        write_word(&mut market, 24, 3);
        let (token_program_key, token_program) = token::keyed_account();
        Self {
            log_key,
            market_key,
            market,
            trader_key,
            trader_base_key: Pubkey::new_unique(),
            trader_base: token_account(base_mint_key, trader_key, 10),
            trader_quote_key: Pubkey::new_unique(),
            trader_quote: token_account(quote_mint_key, trader_key, 20),
            base_mint_key,
            base_vault_key,
            base_vault: token_account(base_mint_key, base_vault_key, 1_000),
            quote_vault_key,
            quote_vault: token_account(quote_mint_key, quote_vault_key, 1_000),
            token_program_key,
            token_program,
        }
    }

    fn instruction(&self, data: &[u8]) -> Instruction {
        Instruction::new_with_bytes(
            PHOENIX_PROGRAM,
            data,
            vec![
                AccountMeta::new_readonly(PHOENIX_PROGRAM, false),
                AccountMeta::new_readonly(self.log_key, false),
                AccountMeta::new(self.market_key, false),
                AccountMeta::new_readonly(self.trader_key, true),
                AccountMeta::new(self.trader_base_key, false),
                AccountMeta::new(self.trader_quote_key, false),
                AccountMeta::new(self.base_vault_key, false),
                AccountMeta::new(self.quote_vault_key, false),
                AccountMeta::new_readonly(self.token_program_key, false),
            ],
        )
    }

    fn accounts(&self) -> Vec<(Pubkey, Account)> {
        vec![
            (
                PHOENIX_PROGRAM,
                mollusk_svm::program::create_program_account_loader_v3(&PHOENIX_PROGRAM),
            ),
            (self.log_key, common::plain_account()),
            (self.market_key, self.market.clone()),
            (self.trader_key, common::plain_account()),
            (self.trader_base_key, self.trader_base.clone()),
            (self.trader_quote_key, self.trader_quote.clone()),
            (self.base_vault_key, self.base_vault.clone()),
            (self.quote_vault_key, self.quote_vault.clone()),
            (self.token_program_key, self.token_program.clone()),
        ]
    }
}

fn assert_raw_reduce_token_rejected(fixture: &RawReduceTokenFixture, instruction: Instruction) {
    let (mollusk, _) = raw_reduce_harness();
    let accounts = fixture.accounts();
    let snapshots: Vec<_> = [2usize, 4, 5, 6, 7]
        .into_iter()
        .map(|index| (accounts[index].0, accounts[index].1.data.clone()))
        .collect();
    let result = mollusk.process_instruction(&instruction, &accounts);
    assert!(
        result.raw_result.is_err(),
        "malformed raw token-context instruction succeeded"
    );
    for (key, before) in snapshots {
        assert_eq!(resulting_account(&result, &key).data, before);
    }
}

fn resulting_account(result: &mollusk_svm::result::InstructionResult, key: &Pubkey) -> Account {
    result
        .resulting_accounts
        .iter()
        .find(|(actual, _)| actual == key)
        .unwrap_or_else(|| panic!("missing resulting account {key}"))
        .1
        .clone()
}

fn phoenix_data_payloads(mollusk: &Mollusk) -> Vec<Vec<u8>> {
    mollusk
        .logger
        .as_ref()
        .expect("raw fixture logger")
        .borrow()
        .get_recorded_content()
        .iter()
        .filter_map(|message| message.strip_prefix("Program data: "))
        .map(|encoded| BASE64.decode(encoded).expect("base64 program data"))
        .collect()
}

fn assert_reduce_header(
    payload: &[u8],
    origin: u8,
    market_sequence: u64,
    market_key: Pubkey,
    trader_key: Pubkey,
) {
    assert_eq!(payload.len(), 93);
    assert_eq!(&payload[..3], &[15, 1, origin]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], trader_key.as_ref());
    assert_eq!(&payload[91..93], &0u16.to_le_bytes());
}

fn assert_reduce_record(
    payload: &[u8],
    origin: u8,
    market_sequence: u64,
    market_key: Pubkey,
    trader_key: Pubkey,
    order_sequence: u64,
    price: u64,
    removed: u64,
    remaining: u64,
) {
    assert_eq!(payload.len(), 128);
    assert_eq!(&payload[..3], &[15, 1, origin]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    // Bytes 11..27 are the runtime clock's unix timestamp and slot.
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], trader_key.as_ref());
    assert_eq!(&payload[91..93], &1u16.to_le_bytes());
    assert_eq!(payload[93], 4);
    assert_eq!(&payload[94..96], &0u16.to_le_bytes());
    assert_eq!(&payload[96..104], &order_sequence.to_le_bytes());
    assert_eq!(&payload[104..112], &price.to_le_bytes());
    assert_eq!(&payload[112..120], &removed.to_le_bytes());
    assert_eq!(&payload[120..128], &remaining.to_le_bytes());
}

fn assert_place_record(
    payload: &[u8],
    market_sequence: u64,
    market_key: Pubkey,
    trader_key: Pubkey,
    order_sequence: u64,
    client_id_low: u64,
    client_id_high: u64,
    price: u64,
    base_lots: u64,
) {
    assert_eq!(payload.len(), 136);
    assert_eq!(&payload[..3], &[15, 1, 3]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], trader_key.as_ref());
    assert_eq!(&payload[91..93], &1u16.to_le_bytes());
    assert_eq!(payload[93], 3);
    assert_eq!(&payload[94..96], &0u16.to_le_bytes());
    assert_eq!(&payload[96..104], &order_sequence.to_le_bytes());
    assert_eq!(&payload[104..112], &client_id_low.to_le_bytes());
    assert_eq!(&payload[112..120], &client_id_high.to_le_bytes());
    assert_eq!(&payload[120..128], &price.to_le_bytes());
    assert_eq!(&payload[128..136], &base_lots.to_le_bytes());
}

fn assert_one_match_batch(
    payload: &[u8],
    market_sequence: u64,
    market_key: Pubkey,
    taker_key: Pubkey,
    maker_key: Pubkey,
    maker_sequence: u64,
    maker_price: u64,
    base_lots: u64,
    remaining_base_lots: u64,
    quote_lots: u64,
    fee: u64,
    client_id_low: u64,
    client_id_high: u64,
) {
    assert_eq!(payload.len(), 203);
    assert_eq!(&payload[..3], &[15, 1, 3]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], taker_key.as_ref());
    assert_eq!(&payload[91..93], &2u16.to_le_bytes());

    let fill = &payload[93..160];
    assert_eq!(fill[0], 2);
    assert_eq!(&fill[1..3], &0u16.to_le_bytes());
    assert_eq!(&fill[3..35], maker_key.as_ref());
    assert_eq!(&fill[35..43], &maker_sequence.to_le_bytes());
    assert_eq!(&fill[43..51], &maker_price.to_le_bytes());
    assert_eq!(&fill[51..59], &base_lots.to_le_bytes());
    assert_eq!(&fill[59..67], &remaining_base_lots.to_le_bytes());

    let summary = &payload[160..203];
    assert_eq!(summary[0], 6);
    assert_eq!(&summary[1..3], &1u16.to_le_bytes());
    assert_eq!(&summary[3..11], &client_id_low.to_le_bytes());
    assert_eq!(&summary[11..19], &client_id_high.to_le_bytes());
    assert_eq!(&summary[19..27], &base_lots.to_le_bytes());
    assert_eq!(&summary[27..35], &quote_lots.to_le_bytes());
    assert_eq!(&summary[35..43], &fee.to_le_bytes());
}

fn assert_two_match_batch(
    payload: &[u8],
    market_sequence: u64,
    market_key: Pubkey,
    taker_key: Pubkey,
    fills: [(Pubkey, u64, u64, u64, u64); 2],
    base_lots: u64,
    quote_lots: u64,
    fee: u64,
    client_id_low: u64,
    client_id_high: u64,
) {
    assert_eq!(payload.len(), 270);
    assert_eq!(&payload[..3], &[15, 1, 3]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], taker_key.as_ref());
    assert_eq!(&payload[91..93], &3u16.to_le_bytes());

    for (index, (maker_key, sequence, price, filled, remaining)) in fills.iter().enumerate() {
        let start = 93 + 67 * index;
        let fill = &payload[start..start + 67];
        assert_eq!(fill[0], 2);
        assert_eq!(&fill[1..3], &(index as u16).to_le_bytes());
        assert_eq!(&fill[3..35], maker_key.as_ref());
        assert_eq!(&fill[35..43], &sequence.to_le_bytes());
        assert_eq!(&fill[43..51], &price.to_le_bytes());
        assert_eq!(&fill[51..59], &filled.to_le_bytes());
        assert_eq!(&fill[59..67], &remaining.to_le_bytes());
    }

    let summary = &payload[227..270];
    assert_eq!(summary[0], 6);
    assert_eq!(&summary[1..3], &2u16.to_le_bytes());
    assert_eq!(&summary[3..11], &client_id_low.to_le_bytes());
    assert_eq!(&summary[11..19], &client_id_high.to_le_bytes());
    assert_eq!(&summary[19..27], &base_lots.to_le_bytes());
    assert_eq!(&summary[27..35], &quote_lots.to_le_bytes());
    assert_eq!(&summary[35..43], &fee.to_le_bytes());
}

fn assert_two_match_and_place_batch(
    payload: &[u8],
    market_sequence: u64,
    market_key: Pubkey,
    taker_key: Pubkey,
    fills: [(Pubkey, u64, u64, u64, u64); 2],
    base_lots: u64,
    quote_lots: u64,
    fee: u64,
    client_id_low: u64,
    client_id_high: u64,
    placed_sequence: u64,
    placed_price: u64,
    placed_base_lots: u64,
) {
    assert_eq!(payload.len(), 313);
    assert_eq!(&payload[..3], &[15, 1, 3]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], taker_key.as_ref());
    assert_eq!(&payload[91..93], &4u16.to_le_bytes());

    for (index, (maker_key, sequence, price, filled, remaining)) in fills.iter().enumerate() {
        let start = 93 + 67 * index;
        let fill = &payload[start..start + 67];
        assert_eq!(fill[0], 2);
        assert_eq!(&fill[1..3], &(index as u16).to_le_bytes());
        assert_eq!(&fill[3..35], maker_key.as_ref());
        assert_eq!(&fill[35..43], &sequence.to_le_bytes());
        assert_eq!(&fill[43..51], &price.to_le_bytes());
        assert_eq!(&fill[51..59], &filled.to_le_bytes());
        assert_eq!(&fill[59..67], &remaining.to_le_bytes());
    }

    let summary = &payload[227..270];
    assert_eq!(summary[0], 6);
    assert_eq!(&summary[1..3], &2u16.to_le_bytes());
    assert_eq!(&summary[3..11], &client_id_low.to_le_bytes());
    assert_eq!(&summary[11..19], &client_id_high.to_le_bytes());
    assert_eq!(&summary[19..27], &base_lots.to_le_bytes());
    assert_eq!(&summary[27..35], &quote_lots.to_le_bytes());
    assert_eq!(&summary[35..43], &fee.to_le_bytes());

    let place = &payload[270..313];
    assert_eq!(place[0], 3);
    assert_eq!(&place[1..3], &3u16.to_le_bytes());
    assert_eq!(&place[3..11], &placed_sequence.to_le_bytes());
    assert_eq!(&place[11..19], &client_id_low.to_le_bytes());
    assert_eq!(&place[19..27], &client_id_high.to_le_bytes());
    assert_eq!(&place[27..35], &placed_price.to_le_bytes());
    assert_eq!(&place[35..43], &placed_base_lots.to_le_bytes());
}

fn assert_one_match_and_place_batch(
    payload: &[u8],
    market_sequence: u64,
    market_key: Pubkey,
    taker_key: Pubkey,
    maker_key: Pubkey,
    maker_sequence: u64,
    maker_price: u64,
    matched_base_lots: u64,
    quote_lots: u64,
    fee: u64,
    client_id_low: u64,
    client_id_high: u64,
    placed_sequence: u64,
    placed_price: u64,
    placed_base_lots: u64,
) {
    assert_eq!(payload.len(), 246);
    assert_eq!(&payload[..3], &[15, 1, 3]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], taker_key.as_ref());
    assert_eq!(&payload[91..93], &3u16.to_le_bytes());

    let fill = &payload[93..160];
    assert_eq!(fill[0], 2);
    assert_eq!(&fill[1..3], &0u16.to_le_bytes());
    assert_eq!(&fill[3..35], maker_key.as_ref());
    assert_eq!(&fill[35..43], &maker_sequence.to_le_bytes());
    assert_eq!(&fill[43..51], &maker_price.to_le_bytes());
    assert_eq!(&fill[51..59], &matched_base_lots.to_le_bytes());
    assert_eq!(&fill[59..67], &0u64.to_le_bytes());

    let summary = &payload[160..203];
    assert_eq!(summary[0], 6);
    assert_eq!(&summary[1..3], &1u16.to_le_bytes());
    assert_eq!(&summary[3..11], &client_id_low.to_le_bytes());
    assert_eq!(&summary[11..19], &client_id_high.to_le_bytes());
    assert_eq!(&summary[19..27], &matched_base_lots.to_le_bytes());
    assert_eq!(&summary[27..35], &quote_lots.to_le_bytes());
    assert_eq!(&summary[35..43], &fee.to_le_bytes());

    let place = &payload[203..246];
    assert_eq!(place[0], 3);
    assert_eq!(&place[1..3], &2u16.to_le_bytes());
    assert_eq!(&place[3..11], &placed_sequence.to_le_bytes());
    assert_eq!(&place[11..19], &client_id_low.to_le_bytes());
    assert_eq!(&place[19..27], &client_id_high.to_le_bytes());
    assert_eq!(&place[27..35], &placed_price.to_le_bytes());
    assert_eq!(&place[35..43], &placed_base_lots.to_le_bytes());
}

fn assert_cancel_all_batch(
    payload: &[u8],
    origin: u8,
    market_sequence: u64,
    market_key: Pubkey,
    trader_key: Pubkey,
    expected: &[(u16, u64, u64, u64)],
) {
    assert_eq!(payload.len(), 93 + 35 * expected.len());
    assert_eq!(&payload[..3], &[15, 1, origin]);
    assert_eq!(&payload[3..11], &market_sequence.to_le_bytes());
    assert_eq!(&payload[27..59], market_key.as_ref());
    assert_eq!(&payload[59..91], trader_key.as_ref());
    assert_eq!(&payload[91..93], &(expected.len() as u16).to_le_bytes());
    for (offset, (event_index, sequence, price, removed)) in expected.iter().enumerate() {
        let record = &payload[93 + 35 * offset..93 + 35 * (offset + 1)];
        assert_eq!(record[0], 4);
        assert_eq!(&record[1..3], &event_index.to_le_bytes());
        assert_eq!(&record[3..11], &sequence.to_le_bytes());
        assert_eq!(&record[11..19], &price.to_le_bytes());
        assert_eq!(&record[19..27], &removed.to_le_bytes());
        assert_eq!(&record[27..35], &0u64.to_le_bytes());
    }
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
fn bounded_map_find_returns_one_based_index_or_zero() {
    let trader_key = [
        0x0706_0504_0302_0100,
        0x1716_1514_1312_1110,
        0x2726_2524_2322_2120,
        0x3736_3534_3332_3130,
    ];
    let trader_market = market_with_first_trader(trader_key);
    run_view_args(
        "findTrader128",
        &trader_key,
        trader_market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    let mut missing_trader = trader_key;
    missing_trader[3] ^= 1;
    run_view_args(
        "findTrader128",
        &missing_trader,
        trader_market.clone(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let bid_key = [55, !7u64];
    let bid_market = run_market_write(
        "insertBid512",
        empty_small_market(),
        true,
        &[bid_key[0], bid_key[1], 3, 9, 0, 0],
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    run_view_args(
        "findBid512",
        &bid_key,
        bid_market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    run_view_args(
        "findBid512",
        &[56, !7u64],
        bid_market,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let ask_key = [44, 8];
    let ask_market = run_market_write(
        "insertAsk512",
        empty_small_market(),
        true,
        &[ask_key[0], ask_key[1], 4, 10, 0, 0],
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    run_view_args(
        "findAsk512",
        &ask_key,
        ask_market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );
    run_view_args(
        "findAsk512",
        &[44, 9],
        ask_market,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut malformed = trader_market;
    write_word(&mut malformed, 8314, packed_u32(1, 0));
    run_view_args(
        "findTrader128",
        &trader_key,
        malformed,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn key_based_order_cursor_follows_fifo_priority_without_retaining_node_addresses() {
    run_view_args(
        "cursorBid512",
        &[0, 0, 0],
        empty_small_market(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let mut bid_market = empty_small_market();
    for (slot, [price, sequence]) in [[50, !3u64], [60, !5u64], [50, !1u64], [40, !7u64]]
        .into_iter()
        .enumerate()
    {
        bid_market = run_market_write(
            "insertBid512",
            bid_market,
            true,
            &[price, sequence, 1, 1, 0, 0],
            &[
                Check::success(),
                Check::return_data(&((slot + 1) as u64).to_le_bytes()),
            ],
        );
    }
    // Bid priority is descending price, then descending encoded sequence. A key between two
    // existing prices proves this is strict upper-bound lookup rather than exact-find + pointer.
    for (args, expected_slot) in [
        ([0, 0, 0], 2u64),
        ([1, 60, !5u64], 3),
        ([1, 55, 0], 3),
        ([1, 50, !1u64], 1),
        ([1, 50, !3u64], 4),
        ([1, 40, !7u64], 0),
    ] {
        run_view_args(
            "cursorBid512",
            &args,
            bid_market.clone(),
            &[
                Check::success(),
                Check::return_data(&expected_slot.to_le_bytes()),
            ],
        );
    }
    run_view_args(
        "cursorBid512",
        &[2, 0, 0],
        bid_market.clone(),
        &[Check::err(ProgramError::Custom(1))],
    );
    bid_market = run_market_write(
        "removeBid512",
        bid_market,
        true,
        &[60, !5u64],
        &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
    );
    // Sokoban's two-child removal transplants another node and changes the tree topology.
    // Re-querying from the removed scalar key still finds the strict logical successor.
    run_view_args(
        "cursorBid512",
        &[1, 60, !5u64],
        bid_market.clone(),
        &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
    );

    let mut ask_market = empty_small_market();
    for (slot, [price, sequence]) in [[50, 3], [40, 5], [50, 1], [60, 7]].into_iter().enumerate() {
        ask_market = run_market_write(
            "insertAsk512",
            ask_market,
            true,
            &[price, sequence, 1, 1, 0, 0],
            &[
                Check::success(),
                Check::return_data(&((slot + 1) as u64).to_le_bytes()),
            ],
        );
    }
    // Ask priority is ascending price, then ascending sequence.
    for (args, expected_slot) in [
        ([0, 0, 0], 2u64),
        ([1, 40, 5], 3),
        ([1, 45, 0], 3),
        ([1, 50, 1], 1),
        ([1, 50, 3], 4),
        ([1, 60, 7], 0),
    ] {
        run_view_args(
            "cursorAsk512",
            &args,
            ask_market.clone(),
            &[
                Check::success(),
                Check::return_data(&expected_slot.to_le_bytes()),
            ],
        );
    }

    // The composed profile validator rejects a cycle before the cursor can follow it forever.
    let root = read_word(&bid_market, BID_TREE_WORD) as usize;
    let root_links_word = BID_TREE_WORD + 4 + 8 * (root - 1);
    write_word(&mut bid_market, root_links_word, packed_u32(root as u32, 0));
    run_view_args(
        "cursorBid512",
        &[0, 0, 0],
        bid_market,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
}

#[test]
fn reduce_order_with_free_funds_composes_bounded_storage_primitives() {
    // Ask partial reduction moves exact base lots from locked to free while retaining the node.
    let mut ask_market = market_with_signer_trader();
    write_word(&mut ask_market, 8322, 10);
    write_word(&mut ask_market, 8323, 2);
    ask_market = run_market_write(
        "insertAsk512",
        ask_market,
        true,
        &[7, 11, 1, 10, 0, 0],
        &[Check::success()],
    );
    let ask_before_zero = ask_market.clone();
    ask_market = run_market_write(
        "reduceAskFreeFunds512",
        ask_market,
        true,
        &[7, 11, 0],
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    assert_eq!(ask_market.data, ask_before_zero.data);
    ask_market = run_market_write(
        "reduceAskFreeFunds512",
        ask_market,
        true,
        &[7, 11, 4],
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    );
    assert_eq!(read_word(&ask_market, 4219), 6);
    assert_eq!(read_word(&ask_market, 8322), 6);
    assert_eq!(read_word(&ask_market, 8323), 6);

    // Oversized reduction uses min(requested, resting), removes the map node, and releases all
    // remaining collateral through the same one-based trader slot.
    ask_market = run_market_write(
        "reduceAskFreeFunds512",
        ask_market,
        true,
        &[7, 11, 100],
        &[Check::success(), Check::return_data(&6u64.to_le_bytes())],
    );
    assert_eq!(read_word(&ask_market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&ask_market, 8322), 0);
    assert_eq!(read_word(&ask_market, 8323), 12);
    run_view(
        "askTreeValid",
        ask_market,
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    // Bid collateral follows price * tick * removed / base-lots-per-unit. For 5 * 3 * 4 / 2,
    // exactly 30 quote lots move from locked to free.
    let mut bid_market = market_with_signer_trader();
    write_word(&mut bid_market, 104, 2);
    write_word(&mut bid_market, 105, 3);
    write_word(&mut bid_market, 8320, 100);
    write_word(&mut bid_market, 8321, 7);
    bid_market = run_market_write(
        "insertBid512",
        bid_market,
        true,
        &[5, !12u64, 1, 10, 0, 0],
        &[Check::success()],
    );
    bid_market = run_market_write(
        "reduceBidFreeFunds512",
        bid_market,
        true,
        &[5, !12u64, 4],
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    );
    assert_eq!(read_word(&bid_market, 119), 6);
    assert_eq!(read_word(&bid_market, 8320), 70);
    assert_eq!(read_word(&bid_market, 8321), 37);

    // Missing orders are successful no-ops even when later bid arithmetic would be invalid.
    write_word(&mut bid_market, 104, 0);
    let missing_before = bid_market.clone();
    bid_market = run_market_write(
        "reduceBidFreeFunds512",
        bid_market,
        true,
        &[6, !99u64, 1],
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    assert_eq!(bid_market.data, missing_before.data);

    // An existing order owned by a different trader is a hard failure and remains atomic.
    let wrong_trader_market = run_market_write(
        "insertAsk512",
        market_with_signer_trader(),
        true,
        &[9, 13, 2, 3, 0, 0],
        &[Check::success()],
    );
    let wrong_trader_after = run_market_write(
        "reduceAskFreeFunds512",
        wrong_trader_market.clone(),
        true,
        &[9, 13, 1],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(wrong_trader_after.data, wrong_trader_market.data);

    // Multiplication overflow is detected before the partial order quantity or trader balances
    // can be stored.
    let mut overflow_market = market_with_signer_trader();
    write_word(&mut overflow_market, 104, 1);
    write_word(&mut overflow_market, 105, 2);
    write_word(&mut overflow_market, 8320, u64::MAX);
    overflow_market = run_market_write(
        "insertBid512",
        overflow_market,
        true,
        &[u64::MAX, !17u64, 1, 2, 0, 0],
        &[Check::success()],
    );
    let overflow_after = run_market_write(
        "reduceBidFreeFunds512",
        overflow_market.clone(),
        true,
        &[u64::MAX, !17u64, 1],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(overflow_after.data, overflow_market.data);
}

#[test]
fn official_raw_place_post_only_bid_locks_quote_and_emits_exact_record() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), trader_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 3);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 300);
    write_word(&mut market, 8320, 7);
    write_word(&mut market, 8321, 100);
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let data = raw_place_data(0, 5, 4, client_id_low, client_id_high);
    let instruction = raw_place_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        market_key,
        true,
        trader_key,
        true,
        seat_key,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            trader_key,
            seat_key,
            seat_account(market_key, trader_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(5, !12u64)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 116), 5);
    assert_eq!(read_word(&market, 117), !12u64);
    assert_eq!(read_word(&market, 118), 1);
    assert_eq!(read_word(&market, 119), 4);
    assert_eq!(read_word(&market, 8320), 37);
    assert_eq!(read_word(&market, 8321), 70);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 13);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 301);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_place_record(
        &payloads[0],
        300,
        market_key,
        trader_key,
        !12u64,
        client_id_low,
        client_id_high,
        5,
        4,
    );
}

#[test]
fn official_raw_place_post_only_ask_locks_base_and_keeps_sequence_domains_separate() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), trader_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_signer_trader();
    write_word(&mut market, ORDER_SEQUENCE_WORD, 7);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 310);
    write_word(&mut market, 8322, 2);
    write_word(&mut market, 8323, 20);
    let data = raw_place_data(1, 9, 6, 44, 55);
    let instruction = raw_place_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        market_key,
        true,
        trader_key,
        true,
        seat_key,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            trader_key,
            seat_key,
            seat_account(market_key, trader_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(9, 7)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4216), 9);
    assert_eq!(read_word(&market, 4217), 7);
    assert_eq!(read_word(&market, 4218), 1);
    assert_eq!(read_word(&market, 4219), 6);
    assert_eq!(read_word(&market, 8322), 8);
    assert_eq!(read_word(&market, 8323), 14);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 311);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_place_record(&payloads[0], 310, market_key, trader_key, 7, 44, 55, 9, 6);
}

#[test]
fn official_raw_limit_bid_completely_fills_one_ask_and_charges_taker_fee() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 400);
    // Maker slot 1 sells four base lots; taker slot 2 pays 20 quote lots plus one fee lot.
    write_word(&mut market, 8322, 4);
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8339, 100);
    write_word(&mut market, 8341, 2);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[5, 9, 1, 4, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(0, 6, 4, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    // Removing a fixed-stride node unlinks and frees its slot; its stale payload is overwritten
    // only when the one-based allocator reuses that slot.
    assert_eq!(read_word(&market, 4219), 4);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8321), 30);
    assert_eq!(read_word(&market, 8339), 79);
    assert_eq!(read_word(&market, 8341), 6);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 401);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_batch(
        &payloads[0],
        400,
        market_key,
        taker_key,
        maker_key,
        9,
        5,
        4,
        0,
        21,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_ask_completely_fills_one_bid_and_charges_taker_fee() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 410);
    let maker_sequence = !9u64;
    // Maker slot 1 buys four base lots; taker slot 2 receives 20 quote lots minus one fee lot.
    write_word(&mut market, 8320, 20);
    write_word(&mut market, 8323, 10);
    write_word(&mut market, 8341, 20);
    write_word(&mut market, 8339, 3);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, maker_sequence, 1, 4, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 44;
    let client_id_high = 55;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(1, 4, 4, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    // Removing a fixed-stride node unlinks and frees its slot; its stale payload is overwritten
    // only when the one-based allocator reuses that slot.
    assert_eq!(read_word(&market, 119), 4);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8323), 14);
    assert_eq!(read_word(&market, 8341), 16);
    assert_eq!(read_word(&market, 8339), 22);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 411);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_batch(
        &payloads[0],
        410,
        market_key,
        taker_key,
        maker_key,
        maker_sequence,
        5,
        4,
        0,
        19,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_bid_partially_fills_one_ask_in_place() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 420);
    // Maker slot 1 sells four base lots; the taker consumes two without moving the node.
    write_word(&mut market, 8322, 4);
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8339, 100);
    write_word(&mut market, 8341, 2);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[5, 9, 1, 4, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(0, 6, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4219), 2);
    assert_eq!(read_word(&market, 8322), 2);
    assert_eq!(read_word(&market, 8321), 20);
    assert_eq!(read_word(&market, 8339), 89);
    assert_eq!(read_word(&market, 8341), 4);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 421);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_batch(
        &payloads[0],
        420,
        market_key,
        taker_key,
        maker_key,
        9,
        5,
        2,
        2,
        11,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_ask_partially_fills_one_bid_in_place() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 430);
    let maker_sequence = !9u64;
    // Maker slot 1 buys four base lots; the taker consumes two without moving the node.
    write_word(&mut market, 8320, 20);
    write_word(&mut market, 8323, 10);
    write_word(&mut market, 8341, 3);
    write_word(&mut market, 8339, 20);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, maker_sequence, 1, 4, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 44;
    let client_id_high = 55;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(1, 4, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 119), 2);
    assert_eq!(read_word(&market, 8320), 10);
    assert_eq!(read_word(&market, 8323), 12);
    assert_eq!(read_word(&market, 8341), 1);
    assert_eq!(read_word(&market, 8339), 29);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 431);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_batch(
        &payloads[0],
        430,
        market_key,
        taker_key,
        maker_key,
        maker_sequence,
        5,
        2,
        2,
        9,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_bid_aggregates_two_distinct_ask_makers() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let first_maker_key = Pubkey::new_unique();
    let second_maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_three_traders(
        pubkey_words(first_maker_key),
        pubkey_words(second_maker_key),
        pubkey_words(taker_key),
    );
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 440);
    // Distinct maker slots sell at successive ask prices. The taker fee is rounded once over
    // adjusted quote 16 + 20, rather than once per Fill.
    write_word(&mut market, 8322, 2);
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8340, 3);
    write_word(&mut market, 8339, 20);
    write_word(&mut market, 8357, 100);
    write_word(&mut market, 8359, 1);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[4, 9, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[5, 10, 2, 2, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data_with_match_limit(0, 6, 4, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8321), 18);
    assert_eq!(read_word(&market, 8340), 1);
    assert_eq!(read_word(&market, 8339), 30);
    assert_eq!(read_word(&market, 8357), 81);
    assert_eq!(read_word(&market, 8359), 5);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 441);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_two_match_batch(
        &payloads[0],
        440,
        market_key,
        taker_key,
        [
            (first_maker_key, 9, 4, 2, 0),
            (second_maker_key, 10, 5, 2, 0),
        ],
        4,
        19,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_ask_aggregates_two_distinct_bid_makers() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let first_maker_key = Pubkey::new_unique();
    let second_maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_three_traders(
        pubkey_words(first_maker_key),
        pubkey_words(second_maker_key),
        pubkey_words(taker_key),
    );
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 450);
    let first_sequence = !9u64;
    let second_sequence = !10u64;
    write_word(&mut market, 8320, 12);
    write_word(&mut market, 8323, 1);
    write_word(&mut market, 8338, 15);
    write_word(&mut market, 8341, 2);
    write_word(&mut market, 8357, 3);
    write_word(&mut market, 8359, 10);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[6, first_sequence, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, second_sequence, 2, 3, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 44;
    let client_id_high = 55;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data_with_match_limit(1, 4, 4, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[Check::success(), Check::return_data(&[])],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 127), 1);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8323), 3);
    assert_eq!(read_word(&market, 8338), 5);
    assert_eq!(read_word(&market, 8341), 4);
    assert_eq!(read_word(&market, 8357), 24);
    assert_eq!(read_word(&market, 8359), 6);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 451);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 12);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_two_match_batch(
        &payloads[0],
        450,
        market_key,
        taker_key,
        [
            (first_maker_key, first_sequence, 6, 2, 0),
            (second_maker_key, second_sequence, 5, 2, 1),
        ],
        4,
        21,
        1,
        client_id_low,
        client_id_high,
    );
}

#[test]
fn official_raw_limit_bid_fills_two_asks_then_posts_non_crossing_remainder() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let first_maker_key = Pubkey::new_unique();
    let second_maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_three_traders(
        pubkey_words(first_maker_key),
        pubkey_words(second_maker_key),
        pubkey_words(taker_key),
    );
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 460);
    // Two crossing makers are consumed. The second maker's third order proves price 7 no longer
    // crosses the taker's limit, so one remaining base lot can rest as a bid at price 6.
    write_word(&mut market, 8322, 2);
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8340, 3);
    write_word(&mut market, 8339, 20);
    write_word(&mut market, 8356, 3);
    write_word(&mut market, 8357, 100);
    write_word(&mut market, 8359, 1);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[4, 9, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[5, 10, 2, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, 11, 2, 1, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let placed_sequence = !12u64;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data_with_match_limit(0, 6, 5, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(6, placed_sequence)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4235), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 116), 6);
    assert_eq!(read_word(&market, 117), placed_sequence);
    assert_eq!(read_word(&market, 118), 3);
    assert_eq!(read_word(&market, 119), 1);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8321), 18);
    assert_eq!(read_word(&market, 8340), 1);
    assert_eq!(read_word(&market, 8339), 30);
    assert_eq!(read_word(&market, 8356), 9);
    assert_eq!(read_word(&market, 8357), 75);
    assert_eq!(read_word(&market, 8359), 5);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 461);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 13);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_two_match_and_place_batch(
        &payloads[0],
        460,
        market_key,
        taker_key,
        [
            (first_maker_key, 9, 4, 2, 0),
            (second_maker_key, 10, 5, 2, 0),
        ],
        4,
        19,
        1,
        client_id_low,
        client_id_high,
        placed_sequence,
        6,
        1,
    );
}

#[test]
fn official_raw_limit_ask_fills_two_bids_then_posts_non_crossing_remainder() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let first_maker_key = Pubkey::new_unique();
    let second_maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_three_traders(
        pubkey_words(first_maker_key),
        pubkey_words(second_maker_key),
        pubkey_words(taker_key),
    );
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 470);
    let first_sequence = !9u64;
    let second_sequence = !10u64;
    let third_sequence = !11u64;
    // Price 3 remains after the two crossing bids and cannot cross a resting ask at price 4.
    write_word(&mut market, 8320, 12);
    write_word(&mut market, 8323, 1);
    write_word(&mut market, 8338, 13);
    write_word(&mut market, 8341, 2);
    write_word(&mut market, 8358, 4);
    write_word(&mut market, 8359, 10);
    write_word(&mut market, 8357, 3);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[6, first_sequence, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, second_sequence, 2, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[3, third_sequence, 2, 1, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 44;
    let client_id_high = 55;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data_with_match_limit(1, 4, 5, 2, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(4, 12)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 135), 1);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4216), 4);
    assert_eq!(read_word(&market, 4217), 12);
    assert_eq!(read_word(&market, 4218), 3);
    assert_eq!(read_word(&market, 4219), 1);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8323), 3);
    assert_eq!(read_word(&market, 8338), 3);
    assert_eq!(read_word(&market, 8341), 4);
    assert_eq!(read_word(&market, 8358), 5);
    assert_eq!(read_word(&market, 8359), 5);
    assert_eq!(read_word(&market, 8357), 24);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 471);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 13);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_two_match_and_place_batch(
        &payloads[0],
        470,
        market_key,
        taker_key,
        [
            (first_maker_key, first_sequence, 6, 2, 0),
            (second_maker_key, second_sequence, 5, 2, 0),
        ],
        4,
        21,
        1,
        client_id_low,
        client_id_high,
        12,
        4,
        1,
    );
}

#[test]
fn official_raw_limit_bid_fills_one_ask_then_posts_non_crossing_remainder() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 440);
    // The first ask is consumed. The second ask proves the posted bid no longer crosses.
    write_word(&mut market, 8322, 3);
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8338, 4);
    write_word(&mut market, 8339, 100);
    write_word(&mut market, 8341, 2);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[5, 9, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, 10, 1, 1, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 0x0706_0504_0302_0100;
    let client_id_high = 0x1716_1514_1312_1110;
    let placed_sequence = !12u64;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(0, 6, 5, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(6, placed_sequence)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4227), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 116), 6);
    assert_eq!(read_word(&market, 117), placed_sequence);
    assert_eq!(read_word(&market, 118), 2);
    assert_eq!(read_word(&market, 119), 3);
    assert_eq!(read_word(&market, 8322), 1);
    assert_eq!(read_word(&market, 8321), 20);
    assert_eq!(read_word(&market, 8338), 22);
    assert_eq!(read_word(&market, 8339), 71);
    assert_eq!(read_word(&market, 8341), 4);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 441);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 13);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_and_place_batch(
        &payloads[0],
        440,
        market_key,
        taker_key,
        maker_key,
        9,
        5,
        2,
        11,
        1,
        client_id_low,
        client_id_high,
        placed_sequence,
        6,
        3,
    );
}

#[test]
fn official_raw_limit_ask_fills_one_bid_then_posts_non_crossing_remainder() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (mollusk, log_key) = raw_reduce_harness();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
    write_word(&mut market, 1, 1);
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 2);
    write_word(&mut market, 107, 100);
    write_word(&mut market, 109, 7);
    write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 450);
    let first_maker_sequence = !9u64;
    let second_maker_sequence = !10u64;
    // The first bid is consumed. The second bid proves the posted ask no longer crosses.
    write_word(&mut market, 8320, 13);
    write_word(&mut market, 8323, 10);
    write_word(&mut market, 8340, 4);
    write_word(&mut market, 8341, 10);
    write_word(&mut market, 8339, 3);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, first_maker_sequence, 1, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[3, second_maker_sequence, 1, 1, 0, 0],
        &[Check::success()],
    );
    let client_id_low = 44;
    let client_id_high = 55;
    let result = mollusk.process_and_validate_instruction(
        &raw_place_instruction(
            &raw_limit_data(1, 4, 5, client_id_low, client_id_high),
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            taker_key,
            true,
            seat_key,
        ),
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            taker_key,
            seat_key,
            seat_account(market_key, taker_key),
        ),
        &[
            Check::success(),
            Check::return_data(&place_return_data(4, 12)),
        ],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 127), 1);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 4216), 4);
    assert_eq!(read_word(&market, 4217), 12);
    assert_eq!(read_word(&market, 4218), 2);
    assert_eq!(read_word(&market, 4219), 3);
    assert_eq!(read_word(&market, 8320), 3);
    assert_eq!(read_word(&market, 8323), 12);
    assert_eq!(read_word(&market, 8340), 7);
    assert_eq!(read_word(&market, 8341), 5);
    assert_eq!(read_word(&market, 8339), 12);
    assert_eq!(read_word(&market, 109), 8);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 451);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 13);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_one_match_and_place_batch(
        &payloads[0],
        450,
        market_key,
        taker_key,
        maker_key,
        first_maker_sequence,
        5,
        2,
        9,
        1,
        client_id_low,
        client_id_high,
        12,
        4,
        3,
    );
}

#[test]
fn official_raw_limit_unsupported_shapes_and_matches_fail_atomically() {
    let taker_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let maker_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), taker_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let prepare = |owner: u64, size: u64, last_slot: u64, taker_quote_free: u64, tick: u64| {
        let mut market = market_with_two_traders(pubkey_words(maker_key), pubkey_words(taker_key));
        write_word(&mut market, 1, 1);
        write_word(&mut market, 104, 2);
        write_word(&mut market, 105, tick);
        write_word(&mut market, 107, 100);
        write_word(&mut market, 109, 7);
        write_word(&mut market, ORDER_SEQUENCE_WORD, 12);
        write_word(&mut market, MARKET_SEQUENCE_WORD, 420);
        write_word(&mut market, 8322, 4);
        write_word(&mut market, 8321, 10);
        write_word(&mut market, 8339, taker_quote_free);
        write_word(&mut market, 8341, 2);
        run_market_write(
            "insertAsk512",
            market,
            true,
            &[5, 9, owner, size, last_slot, 0],
            &[Check::success()],
        )
    };
    let canonical = raw_limit_data(0, 6, 4, 1, 2);
    let valid_market = prepare(1, 4, 0, 100, 3);
    let uninitialized_order_sequence = {
        let mut market = valid_market.clone();
        write_word(&mut market, ORDER_SEQUENCE_WORD, 0);
        market
    };
    let crossing_remainder = run_market_write(
        "insertAsk512",
        prepare(1, 2, 0, 100, 3),
        true,
        &[6, 10, 1, 1, 0, 0],
        &[Check::success()],
    );
    let mut cases: Vec<(&str, Vec<u8>, Account)> = vec![
        ("short wire", canonical[..48].to_vec(), valid_market.clone()),
        (
            "long wire",
            {
                let mut data = canonical.clone();
                data.push(0);
                data
            },
            valid_market.clone(),
        ),
        (
            "noncrossing",
            raw_limit_data(0, 4, 4, 1, 2),
            valid_market.clone(),
        ),
        (
            "remainder still crosses after match limit",
            raw_limit_data(0, 6, 5, 1, 2),
            crossing_remainder,
        ),
        (
            "uninitialized order sequence",
            canonical.clone(),
            uninitialized_order_sequence,
        ),
        ("self match", canonical.clone(), prepare(2, 4, 0, 100, 3)),
        ("maker TIF", canonical.clone(), prepare(1, 4, 1, 100, 3)),
        (
            "insufficient funds",
            canonical.clone(),
            prepare(1, 4, 0, 0, 3),
        ),
        (
            "quote overflow",
            canonical.clone(),
            prepare(1, 4, 0, 100, u64::MAX),
        ),
    ];
    for (label, offset, value) in [
        ("wrong variant", 1, 2),
        ("unsupported self-trade policy", 19, 1),
        ("missing match limit", 20, 0),
        ("non-deposited funds", 45, 0),
        ("slot TIF", 46, 1),
        ("time TIF", 47, 1),
        ("silent funds failure", 48, 1),
    ] {
        let mut data = canonical.clone();
        data[offset] = value;
        cases.push((label, data, valid_market.clone()));
    }
    let mut wrong_match_limit = canonical.clone();
    wrong_match_limit[21..29].copy_from_slice(&3u64.to_le_bytes());
    cases.push(("unsupported match limit", wrong_match_limit, valid_market));

    for (label, data, market) in cases {
        let before = market.data.clone();
        let (mollusk, log_key) = raw_reduce_harness();
        let result = mollusk.process_instruction(
            &raw_place_instruction(
                &data,
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                true,
                taker_key,
                true,
                seat_key,
            ),
            &raw_place_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market,
                taker_key,
                seat_key,
                seat_account(market_key, taker_key),
            ),
        );
        assert!(
            result.raw_result.is_err(),
            "unsupported Limit case succeeded: {label}"
        );
        assert_eq!(
            resulting_account(&result, &market_key).data,
            before,
            "market mutated for rejected Limit case: {label}"
        );
        assert!(
            phoenix_data_payloads(&mollusk).is_empty(),
            "audit emitted for rejected Limit case: {label}"
        );
    }
}

#[test]
fn official_raw_place_rejects_noncanonical_wire_before_storage_or_audit() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), trader_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let mut market = market_with_signer_trader();
    write_word(&mut market, 8321, 100);
    let before = market.data.clone();
    let canonical = raw_place_data(0, 5, 4, 1, 2);
    let mut cases = vec![canonical[..39].to_vec(), {
        let mut data = canonical.clone();
        data.push(0);
        data
    }];
    for (offset, value) in [(1, 1), (2, 2), (35, 2), (36, 0), (37, 1), (38, 1), (39, 1)] {
        let mut data = canonical.clone();
        data[offset] = value;
        cases.push(data);
    }
    for data in cases {
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_place_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            trader_key,
            true,
            seat_key,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_place_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market.clone(),
                trader_key,
                seat_key,
                seat_account(market_key, trader_key),
            ),
        );
        assert!(
            result.raw_result.is_err(),
            "noncanonical wire succeeded: {data:?}"
        );
        assert_eq!(resulting_account(&result, &market_key).data, before);
        assert!(phoenix_data_payloads(&mollusk).is_empty());
    }
}

#[test]
fn official_raw_place_strict_slice_rejects_crossing_and_inactive_markets_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), trader_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let data = raw_place_data(0, 5, 4, 1, 2);

    let mut crossing = market_with_signer_trader();
    write_word(&mut crossing, 8321, 100);
    crossing = run_market_write(
        "insertAsk512",
        crossing,
        true,
        &[6, 1, 1, 1, 0, 0],
        &[Check::success()],
    );
    let mut inactive = market_with_signer_trader();
    write_word(&mut inactive, 1, 0);
    write_word(&mut inactive, 8321, 100);

    for market in [crossing, inactive] {
        let before = market.data.clone();
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_place_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            true,
            trader_key,
            true,
            seat_key,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_place_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market,
                trader_key,
                seat_key,
                seat_account(market_key, trader_key),
            ),
        );
        assert!(result.raw_result.is_err());
        assert_eq!(resulting_account(&result, &market_key).data, before);
        assert!(phoenix_data_payloads(&mollusk).is_empty());
    }
}

#[test]
fn official_raw_place_authenticates_seat_and_fails_atomically_without_collateral() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let (seat_key, _) = Pubkey::find_program_address(
        &[b"seat", market_key.as_ref(), trader_key.as_ref()],
        &PHOENIX_PROGRAM,
    );
    let data = raw_place_data(0, 5, 4, 1, 2);

    let mut invalid_seats = Vec::new();
    let mut wrong_discriminator = seat_account(market_key, trader_key);
    write_word(&mut wrong_discriminator, 0, 0);
    invalid_seats.push((seat_key, wrong_discriminator, true, true));
    let mut unapproved = seat_account(market_key, trader_key);
    write_word(&mut unapproved, 9, 0);
    invalid_seats.push((seat_key, unapproved, true, true));
    let mut wrong_trader = seat_account(market_key, trader_key);
    write_pubkey(&mut wrong_trader, 40, Pubkey::new_unique());
    invalid_seats.push((seat_key, wrong_trader, true, true));
    let mut wrong_owner = seat_account(market_key, trader_key);
    wrong_owner.owner = Pubkey::new_unique();
    invalid_seats.push((seat_key, wrong_owner, true, true));
    invalid_seats.push((
        Pubkey::new_unique(),
        seat_account(market_key, trader_key),
        true,
        true,
    ));
    invalid_seats.push((seat_key, seat_account(market_key, trader_key), false, true));
    invalid_seats.push((seat_key, seat_account(market_key, trader_key), true, false));

    for (actual_seat_key, seat, trader_signer, market_writable) in invalid_seats {
        let mut market = market_with_signer_trader();
        write_word(&mut market, 8321, 100);
        let before = market.data.clone();
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_place_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market_writable,
            trader_key,
            trader_signer,
            actual_seat_key,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_place_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market,
                trader_key,
                actual_seat_key,
                seat,
            ),
        );
        assert!(result.raw_result.is_err());
        assert_eq!(resulting_account(&result, &market_key).data, before);
        assert!(phoenix_data_payloads(&mollusk).is_empty());
    }

    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 320);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_place_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        market_key,
        true,
        trader_key,
        true,
        seat_key,
    );
    let result = mollusk.process_instruction(
        &instruction,
        &raw_place_accounts(
            PHOENIX_PROGRAM,
            log_key,
            market_key,
            market,
            trader_key,
            seat_key,
            seat_account(market_key, trader_key),
        ),
    );
    assert!(result.raw_result.is_err());
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());
}

#[test]
fn official_raw_cancel_all_free_funds_missing_trader_is_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = empty_small_market();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 60);
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_all_data(7),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 61);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 7, 60, market_key, trader_key);
}

#[test]
fn official_raw_cancel_all_withdraw_missing_trader_is_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = empty_small_market();
    write_word(&mut market, 1, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 70);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_cancel_all_data(6)),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 71);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        10
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 6, 70, market_key, trader_key);
}

#[test]
fn official_raw_cancel_all_free_funds_is_bids_then_asks_and_owner_filtered() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let foreign_key = Pubkey::new_unique();
    let mut market = run_market_write(
        "registerSecondTrader128",
        market_with_signer_trader(),
        true,
        &pubkey_words(foreign_key),
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    );
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 80);
    write_word(&mut market, 8320, 39);
    write_word(&mut market, 8321, 5);
    write_word(&mut market, 8322, 10);
    write_word(&mut market, 8323, 6);
    for args in [
        [9, !1u64, 1, 2, 0, 0],
        [8, !2u64, 2, 5, 0, 0],
        [7, !3u64, 1, 3, 0, 0],
    ] {
        market = run_market_write("insertBid512", market, true, &args, &[Check::success()]);
    }
    for args in [[3, 4, 1, 4, 0, 0], [4, 5, 2, 5, 0, 0], [5, 6, 1, 6, 0, 0]] {
        market = run_market_write("insertAsk512", market, true, &args, &[Check::success()]);
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_all_data(7),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 81);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 44);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8323), 16);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        7,
        80,
        market_key,
        trader_key,
        &[
            (0, !1u64, 9, 2),
            (1, !3u64, 7, 3),
            (2, 4, 3, 4),
            (3, 6, 5, 6),
        ],
    );
}

#[test]
fn official_raw_cancel_all_withdraws_only_newly_released_quote_then_base() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let bid_sequence = !10u64;
    let ask_sequence = 11u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 100);
    write_word(&mut market, 8320, 20);
    write_word(&mut market, 8321, 7);
    write_word(&mut market, 8322, 3);
    write_word(&mut market, 8323, 8);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, bid_sequence, 1, 4, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[2, ask_sequence, 1, 3, 0, 0],
        &[Check::success()],
    );
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_cancel_all_data(6)),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 101);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 7);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8323), 8);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        940
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        80
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        994
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        16
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        6,
        100,
        market_key,
        trader_key,
        &[(0, bid_sequence, 5, 4), (1, ask_sequence, 2, 3)],
    );
}

#[test]
fn official_raw_cancel_all_flushes_32_records_without_resetting_event_index() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 120);
    write_word(&mut market, 8320, 33);
    for index in 0..33u64 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[1, !(index + 1), 1, 1, 0, 0],
            &[Check::success()],
        );
    }
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_all_data(7),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 121);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 33);

    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 2);
    let first: Vec<_> = (0..32u16)
        .map(|index| (index, !(u64::from(index) + 1), 1, 1))
        .collect();
    assert_cancel_all_batch(&payloads[0], 7, 120, market_key, trader_key, &first);
    assert_cancel_all_batch(
        &payloads[1],
        7,
        120,
        market_key,
        trader_key,
        &[(32, !33u64, 1, 1)],
    );
}

#[test]
fn official_raw_cancel_all_rejects_malformed_storage_before_mutation_or_audit() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 140);
    write_word(&mut market, 8320, 1);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[1, !1u64, 1, 1, 0, 0],
        &[Check::success()],
    );
    // A nonzero parent on the root violates the complete FIFO-tree validator.
    write_word(&mut market, 115, 1);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_all_data(7),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
    );
    assert!(result.raw_result.is_err());
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());
}

#[test]
fn official_raw_cancel_all_rejects_uninitialized_order_sequence_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = empty_small_market();
    write_word(&mut market, ORDER_SEQUENCE_WORD, 0);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_all_data(7),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
    );
    assert!(result.raw_result.is_err());
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());
}

#[test]
fn official_raw_cancel_all_rejects_invalid_token_context_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 150);
    write_word(&mut market, 8322, 1);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[1, 1, 1, 1, 0, 0],
        &[Check::success()],
    );
    let mut fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    write_word(&mut fixture.market, 1, 0);
    assert_raw_reduce_token_rejected(&fixture, fixture.instruction(&raw_cancel_all_data(6)));
}

#[test]
fn official_raw_cancel_up_to_searches_before_filters_and_honors_bid_tick_and_cancel_caps() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let foreign_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let mut market = run_market_write(
        "registerSecondTrader128",
        market_with_signer_trader(),
        true,
        &pubkey_words(foreign_key),
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    );
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 160);
    write_word(&mut market, 8320, 70);
    write_word(&mut market, 8321, 5);
    write_word(&mut market, 8322, 4);
    for args in [
        [10, !1u64, 2, 1, 0, 0],
        [9, !2u64, 1, 2, 0, 0],
        [8, !3u64, 1, 3, 0, 0],
    ] {
        market = run_market_write("insertBid512", market, true, &args, &[Check::success()]);
    }
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[1, 4, 1, 4, 0, 0],
        &[Check::success()],
    );

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(9, 0, Some(9), Some(2), Some(2));
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    // The foreign best order consumes one search slot. The inclusive price-9 owned order is the
    // only cancellation; price 8 and the unselected ask side remain.
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 161);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 2);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 8320), 52);
    assert_eq!(read_word(&market, 8321), 23);
    assert_eq!(read_word(&market, 8322), 4);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        9,
        160,
        market_key,
        trader_key,
        &[(0, !2u64, 9, 2)],
    );
}

#[test]
fn official_raw_cancel_up_to_none_defaults_cancel_only_the_selected_side() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    // Tag 9 does not enter the CancelOrWithdraw status gate.
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 170);
    write_word(&mut market, 8320, 5);
    write_word(&mut market, 8322, 5);
    write_word(&mut market, 8323, 6);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, !1u64, 1, 1, 0, 0],
        &[Check::success()],
    );
    for args in [[3, 1, 1, 2, 0, 0], [4, 2, 1, 3, 0, 0]] {
        market = run_market_write("insertAsk512", market, true, &args, &[Check::success()]);
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(9, 1, None, None, None);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 5);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8323), 11);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_cancel_all_batch(
        &payloads[0],
        9,
        170,
        market_key,
        trader_key,
        &[(0, 1, 3, 2), (1, 2, 4, 3)],
    );
}

#[test]
fn official_raw_cancel_up_to_cancel_cap_preserves_equal_price_fifo() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 175);
    write_word(&mut market, 8320, 10);
    for args in [[5, !1u64, 1, 1, 0, 0], [5, !2u64, 1, 1, 0, 0]] {
        market = run_market_write("insertBid512", market, true, &args, &[Check::success()]);
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(9, 0, Some(5), None, Some(1));
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success()],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 8320), 5);
    assert_eq!(read_word(&market, 8321), 5);
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        9,
        175,
        market_key,
        trader_key,
        &[(0, !1u64, 5, 1)],
    );
}

#[test]
fn official_raw_cancel_up_to_ask_tick_is_inclusive() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 180);
    write_word(&mut market, 8322, 6);
    for args in [[3, 1, 1, 1, 0, 0], [4, 2, 1, 2, 0, 0], [5, 3, 1, 3, 0, 0]] {
        market = run_market_write("insertAsk512", market, true, &args, &[Check::success()]);
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(9, 1, Some(4), None, None);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success()],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 1);
    assert_eq!(read_word(&market, 8322), 3);
    assert_eq!(read_word(&market, 8323), 3);
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        9,
        180,
        market_key,
        trader_key,
        &[(0, 1, 3, 1), (1, 2, 4, 2)],
    );
}

#[test]
fn official_raw_cancel_up_to_some_zero_limits_are_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    for (sequence, search, cancel) in [(190, Some(0), None), (191, None, Some(0))] {
        let market_key = Pubkey::new_unique();
        let mut market = market_with_signer_trader();
        write_word(&mut market, 104, 1);
        write_word(&mut market, 105, 1);
        write_word(&mut market, MARKET_SEQUENCE_WORD, sequence);
        write_word(&mut market, 8320, 5);
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[5, !1u64, 1, 1, 0, 0],
            &[Check::success()],
        );
        let before = market.data.clone();
        let (mollusk, log_key) = raw_reduce_harness();
        let data = raw_cancel_up_to_data(9, 0, None, search, cancel);
        let instruction = raw_reduce_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_and_validate_instruction(
            &instruction,
            &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
            &[Check::success()],
        );
        let market = resulting_account(&result, &market_key);
        assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), sequence + 1);
        assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
        assert_eq!(read_word(&market, BID_TREE_WORD + 2), 1);
        assert_eq!(
            &market.data[0..MARKET_SEQUENCE_WORD * 8],
            &before[0..MARKET_SEQUENCE_WORD * 8]
        );
        let payloads = phoenix_data_payloads(&mollusk);
        assert_eq!(payloads.len(), 1);
        assert_reduce_header(&payloads[0], 9, sequence, market_key, trader_key);
    }
}

#[test]
fn official_raw_cancel_up_to_withdraw_claims_each_order_and_preserves_free_funds() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 200);
    write_word(&mut market, 8320, 14);
    write_word(&mut market, 8321, 7);
    for args in [[5, !1u64, 1, 2, 0, 0], [2, !2u64, 1, 2, 0, 0]] {
        market = run_market_write("insertBid512", market, true, &args, &[Check::success()]);
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(8, 0, None, None, None);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 201);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 7);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        958
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        62
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        8,
        200,
        market_key,
        trader_key,
        &[(0, !1u64, 5, 2), (1, !2u64, 2, 2)],
    );
}

#[test]
fn official_raw_cancel_up_to_missing_trader_and_no_price_match_are_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    for (sequence, mut market, tick) in [
        (210, empty_small_market(), None),
        (211, market_with_signer_trader(), Some(6)),
    ] {
        let market_key = Pubkey::new_unique();
        write_word(&mut market, 104, 1);
        write_word(&mut market, 105, 1);
        write_word(&mut market, MARKET_SEQUENCE_WORD, sequence);
        if tick.is_some() {
            write_word(&mut market, 8320, 5);
            market = run_market_write(
                "insertBid512",
                market,
                true,
                &[5, !1u64, 1, 1, 0, 0],
                &[Check::success()],
            );
        }
        let (mollusk, log_key) = raw_reduce_harness();
        let data = raw_cancel_up_to_data(9, 0, tick, None, None);
        let instruction = raw_reduce_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_and_validate_instruction(
            &instruction,
            &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
            &[Check::success()],
        );
        assert_eq!(
            read_word(
                &resulting_account(&result, &market_key),
                MARKET_SEQUENCE_WORD
            ),
            sequence + 1
        );
        let payloads = phoenix_data_payloads(&mollusk);
        assert_eq!(payloads.len(), 1);
        assert_reduce_header(&payloads[0], 9, sequence, market_key, trader_key);
    }
}

#[test]
fn official_raw_cancel_up_to_rejects_noncanonical_borsh_and_invalid_side_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 220);
    let before = market.data.clone();
    for data in [
        vec![9, 0, 2, 0, 0],
        vec![9, 0, 0, 2, 0],
        vec![9, 0, 0, 0, 2],
        vec![9, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        vec![9, 0, 0, 1, 0, 0, 0],
        vec![9, 0, 0, 0, 1, 0, 0, 0],
        vec![9, 0, 0, 0, 0, 0],
        raw_cancel_up_to_data(9, 2, None, None, None),
    ] {
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_reduce_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_reduce_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market.clone(),
                trader_key,
            ),
        );
        assert!(result.raw_result.is_err());
        assert_eq!(resulting_account(&result, &market_key).data, before);
        assert!(phoenix_data_payloads(&mollusk).is_empty());
    }
}

#[test]
fn official_raw_cancel_up_to_rejects_malformed_storage_and_token_context_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 230);
    write_word(&mut market, 8320, 1);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[1, !1u64, 1, 1, 0, 0],
        &[Check::success()],
    );
    write_word(&mut market, 115, 1);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_up_to_data(9, 0, None, None, None);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
    );
    assert!(result.raw_result.is_err());
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());

    let token_market_key = Pubkey::new_unique();
    let mut token_market = market_with_signer_trader();
    write_word(&mut token_market, MARKET_SEQUENCE_WORD, 231);
    let mut fixture = RawReduceTokenFixture::new(token_market_key, trader_key, token_market);
    write_word(&mut fixture.market, 1, 0);
    assert_raw_reduce_token_rejected(
        &fixture,
        fixture.instruction(&raw_cancel_up_to_data(8, 0, None, None, None)),
    );
}

#[test]
fn official_raw_cancel_by_id_empty_vec_is_noop_without_sequence_or_audit() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 1, 0);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 240);
    write_word(&mut market, 8320, 9);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_cancel_by_id_data(11, &[]),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());
}

#[test]
fn official_raw_cancel_by_id_free_funds_cancels_owned_bid_and_keeps_collateral() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence = !11u64;
    let mut market = market_with_signer_trader();
    // Tag 11 skips the CancelOrWithdraw status gate.
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 250);
    write_word(&mut market, 8320, 20);
    write_word(&mut market, 8321, 3);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence, 1, 4, 0, 0],
        &[Check::success()],
    );

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_by_id_data(11, &[(0, 5, sequence)]);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 251);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 23);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        11,
        250,
        market_key,
        trader_key,
        &[(0, sequence, 5, 4)],
    );
}

#[test]
fn official_raw_cancel_by_id_free_funds_cancels_two_owned_bids_in_one_vec() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence_a = !21u64;
    let sequence_b = !22u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 280);
    // Pre-seed quote locked to the sum of both resting bids (5*3 + 6*2); inserts do not
    // adjust trader quote words in this fixture path.
    write_word(&mut market, 8320, 27);
    write_word(&mut market, 8321, 8);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence_a, 1, 3, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[6, sequence_b, 1, 2, 0, 0],
        &[Check::success()],
    );

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_by_id_data(11, &[(0, 5, sequence_a), (0, 6, sequence_b)]);
    assert_eq!(data.len(), 39);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 281);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 35);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        11,
        280,
        market_key,
        trader_key,
        &[(0, sequence_a, 5, 3), (0, sequence_b, 6, 2)],
    );
}

#[test]
fn official_raw_cancel_by_id_free_funds_cancels_four_owned_bids_in_one_vec() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!41u64, !42u64, !43u64, !44u64];
    let prices = [5u64, 6, 7, 8];
    let sizes = [1u64, 2, 3, 4];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 300);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 9);
    for i in 0..4 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..4).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(11, &orders);
    assert_eq!(data.len(), 73);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 301);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 9 + locked);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    let expected: Vec<(u16, u64, u64, u64)> = (0..4)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &payloads[0],
        11,
        300,
        market_key,
        trader_key,
        &expected,
    );
}


#[test]
fn official_raw_cancel_by_id_free_funds_cancels_eight_owned_bids_in_one_vec() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!41u64, !42u64, !43u64, !44u64, !45u64, !46u64, !47u64, !48u64];
    let prices = [5u64, 6, 7, 8, 9, 10, 11, 12];
    let sizes = [1u64, 1, 1, 1, 1, 1, 1, 1];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 400);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 9);
    for i in 0..8 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }

    let (mollusk, log_key) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..8).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(11, &orders);
    assert_eq!(data.len(), 141);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 401);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 9 + locked);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    let expected: Vec<(u16, u64, u64, u64)> = (0..8)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &payloads[0],
        11,
        400,
        market_key,
        trader_key,
        &expected,
    );
}

#[test]
fn official_raw_cancel_by_id_free_funds_cancels_owned_bid_and_ask_in_one_vec() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence_bid = !31u64;
    let sequence_ask = 32u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 1, 0);
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 290);
    // Bid quote lock 5*3=15; ask base lock = size 4. Inserts do not adjust trader words here.
    write_word(&mut market, 8320, 15);
    write_word(&mut market, 8321, 2);
    write_word(&mut market, 8322, 4);
    write_word(&mut market, 8323, 1);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence_bid, 1, 3, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, sequence_ask, 1, 4, 0, 0],
        &[Check::success()],
    );

    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_by_id_data(11, &[(0, 5, sequence_bid), (1, 7, sequence_ask)]);
    assert_eq!(data.len(), 39);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 291);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 17);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8323), 5);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_cancel_all_batch(
        &payloads[0],
        11,
        290,
        market_key,
        trader_key,
        &[(0, sequence_bid, 5, 3), (0, sequence_ask, 7, 4)],
    );
}

#[test]
fn official_raw_cancel_by_id_skips_missing_side_mismatch_and_foreign_owner() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let foreign_key = Pubkey::new_unique();
    let market_key = Pubkey::new_unique();
    let mut market = run_market_write(
        "registerSecondTrader128",
        market_with_signer_trader(),
        true,
        &pubkey_words(foreign_key),
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    );
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 260);
    write_word(&mut market, 8320, 10);
    write_word(&mut market, 8322, 6);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[4, !1u64, 2, 2, 0, 0],
        &[Check::success()],
    );
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[3, 2, 1, 3, 0, 0],
        &[Check::success()],
    );
    let before_tree = (
        read_word(&market, BID_TREE_WORD + 2),
        read_word(&market, ASK_TREE_WORD + 2),
        read_word(&market, 8320),
        read_word(&market, 8322),
    );

    for (label, orders) in [
        ("missing", vec![(0, 9, !99u64)]),
        ("side_mismatch", vec![(1, 4, !1u64)]),
        ("foreign", vec![(0, 4, !1u64)]),
    ] {
        let (mollusk, log_key) = raw_reduce_harness();
        let data = raw_cancel_by_id_data(11, &orders);
        let instruction = raw_reduce_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_and_validate_instruction(
            &instruction,
            &raw_reduce_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market.clone(),
                trader_key,
            ),
            &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
        );
        let after = resulting_account(&result, &market_key);
        assert_eq!(
            read_word(&after, MARKET_SEQUENCE_WORD),
            261,
            "{label} must still bump market sequence"
        );
        assert_eq!(
            (
                read_word(&after, BID_TREE_WORD + 2),
                read_word(&after, ASK_TREE_WORD + 2),
                read_word(&after, 8320),
                read_word(&after, 8322),
            ),
            before_tree,
            "{label} must leave books untouched"
        );
        let payloads = phoenix_data_payloads(&mollusk);
        assert_eq!(payloads.len(), 1, "{label}");
        assert_reduce_header(&payloads[0], 11, 260, market_key, trader_key);
    }
}

#[test]
fn official_raw_cancel_by_id_withdraw_claims_released_quote_and_preserves_free() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence = !7u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 270);
    write_word(&mut market, 8320, 15);
    write_word(&mut market, 8321, 4);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence, 1, 3, 0, 0],
        &[Check::success()],
    );
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_cancel_by_id_data(10, &[(0, 5, sequence)]);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 271);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 4);
    // quoteLots = price*size = 15; fixture quoteLotSize = 3 → 45 atoms.
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        955
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        65
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        270,
        market_key,
        trader_key,
        &[(0, sequence, 5, 3)],
    );
}

#[test]
fn official_raw_cancel_by_id_withdraw_cancels_four_owned_bids_and_claims_quote() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!51u64, !52u64, !53u64, !54u64];
    let prices = [5u64, 6, 7, 8];
    let sizes = [1u64, 2, 3, 4];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    // quoteLotSize in fixture = 3 → released quote atoms = locked * 3.
    let quote_atoms = locked * 3;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 310);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 4);
    for i in 0..4 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..4).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(10, &orders);
    assert_eq!(data.len(), 73);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 311);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 4);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1000 - quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20 + quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let expected: Vec<(u16, u64, u64, u64)> = (0..4)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        310,
        market_key,
        trader_key,
        &expected,
    );
}

#[test]
fn official_raw_cancel_by_id_withdraw_cancels_five_owned_bids_and_claims_quote() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!51u64, !52u64, !53u64, !54u64, !55u64];
    let prices = [5u64, 6, 7, 8, 9];
    let sizes = [1u64, 2, 3, 4, 1];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    // quoteLotSize in fixture = 3 → released quote atoms = locked * 3.
    let quote_atoms = locked * 3;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 310);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 5);
    for i in 0..5 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..5).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(10, &orders);
    assert_eq!(data.len(), 90);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 311);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 5);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1000 - quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20 + quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let expected: Vec<(u16, u64, u64, u64)> = (0..5)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        310,
        market_key,
        trader_key,
        &expected,
    );
}

#[test]
fn official_raw_cancel_by_id_withdraw_cancels_six_owned_bids_and_claims_quote() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!51u64, !52u64, !53u64, !54u64, !55u64, !56u64];
    let prices = [5u64, 6, 7, 8, 9, 10];
    let sizes = [1u64, 2, 3, 4, 1, 2];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    // quoteLotSize in fixture = 3 → released quote atoms = locked * 3.
    let quote_atoms = locked * 3;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 320);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 6);
    for i in 0..6 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..6).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(10, &orders);
    assert_eq!(data.len(), 107);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 321);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 6);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1000 - quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20 + quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let expected: Vec<(u16, u64, u64, u64)> = (0..6)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        320,
        market_key,
        trader_key,
        &expected,
    );
}

#[test]
fn official_raw_cancel_by_id_withdraw_cancels_seven_owned_bids_and_claims_quote() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!51u64, !52u64, !53u64, !54u64, !55u64, !56u64, !57u64];
    let prices = [5u64, 6, 7, 8, 9, 10, 11];
    let sizes = [1u64, 2, 3, 4, 1, 2, 1];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    // quoteLotSize in fixture = 3 → released quote atoms = locked * 3.
    let quote_atoms = locked * 3;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 330);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 7);
    for i in 0..7 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..7).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(10, &orders);
    assert_eq!(data.len(), 124);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 331);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 7);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1000 - quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20 + quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let expected: Vec<(u16, u64, u64, u64)> = (0..7)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        330,
        market_key,
        trader_key,
        &expected,
    );
}

fn official_raw_cancel_by_id_withdraw_cancels_eight_owned_bids_and_claims_quote() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequences = [!51u64, !52u64, !53u64, !54u64, !55u64, !56u64, !57u64, !58u64];
    let prices = [5u64, 6, 7, 8, 9, 10, 11, 12];
    let sizes = [1u64, 2, 3, 4, 1, 2, 1, 2];
    let locked: u64 = prices
        .iter()
        .zip(sizes.iter())
        .map(|(p, s)| p * s)
        .sum();
    // quoteLotSize in fixture = 3 → released quote atoms = locked * 3.
    let quote_atoms = locked * 3;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 340);
    write_word(&mut market, 8320, locked);
    write_word(&mut market, 8321, 8);
    for i in 0..8 {
        market = run_market_write(
            "insertBid512",
            market,
            true,
            &[prices[i], sequences[i], 1, sizes[i], 0, 0],
            &[Check::success()],
        );
    }
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let orders: Vec<(u8, u64, u64)> = (0..8).map(|i| (0, prices[i], sequences[i])).collect();
    let data = raw_cancel_by_id_data(10, &orders);
    assert_eq!(data.len(), 141);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 341);
    assert_eq!(read_word(&market, BID_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8320), 0);
    assert_eq!(read_word(&market, 8321), 8);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1000 - quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        20 + quote_atoms
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let expected: Vec<(u16, u64, u64, u64)> = (0..8)
        .map(|i| (0, sequences[i], prices[i], sizes[i]))
        .collect();
    assert_cancel_all_batch(
        &phoenix_data_payloads(&mollusk)[0],
        10,
        340,
        market_key,
        trader_key,
        &expected,
    );
}

#[test]
fn official_raw_withdraw_funds_claims_quote_and_base_from_free() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 400);
    // quoteFree=8321, baseFree=8323 for trader index 1; lot sizes are 3 / 2 in the token fixture.
    write_word(&mut market, 8321, 10);
    write_word(&mut market, 8323, 7);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_withdraw_funds_data(Some(5), Some(3));
    assert_eq!(data.len(), 19);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 401);
    assert_eq!(read_word(&market, 8321), 5);
    assert_eq!(read_word(&market, 8323), 4);
    // quote atoms = 5 * 3 = 15; base atoms = 3 * 2 = 6.
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        985
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        35
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        994
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        16
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 12, 400, market_key, trader_key);
}

#[test]
fn official_raw_withdraw_funds_zero_zero_is_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 410);
    write_word(&mut market, 8321, 9);
    write_word(&mut market, 8323, 8);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_withdraw_funds_data(Some(0), Some(0));
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 411);
    assert_eq!(read_word(&market, 8321), 9);
    assert_eq!(read_word(&market, 8323), 8);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1_000
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 12, 410, market_key, trader_key);
}

#[test]
fn official_raw_withdraw_funds_none_none_drains_all_free() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 415);
    // quoteFree=8321, baseFree=8323 for trader index 1; lot sizes are 3 / 2 in the token fixture.
    write_word(&mut market, 8321, 6);
    write_word(&mut market, 8323, 4);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_withdraw_funds_data(None, None);
    assert_eq!(data.len(), 3);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 416);
    assert_eq!(read_word(&market, 8321), 0);
    assert_eq!(read_word(&market, 8323), 0);
    // quote atoms = 6 * 3 = 18; base atoms = 4 * 2 = 8.
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        982
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        38
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        992
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        18
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 12, 415, market_key, trader_key);
}

fn official_raw_withdraw_funds_rejects_insufficient_free_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 420);
    write_word(&mut market, 8321, 2);
    write_word(&mut market, 8323, 1);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    assert_raw_reduce_token_rejected(&fixture, fixture.instruction(&raw_withdraw_funds_data(Some(3), Some(0))));
}

#[test]
fn official_raw_deposit_funds_credits_quote_and_base_free() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 500);
    write_word(&mut market, 8321, 4);
    write_word(&mut market, 8323, 2);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_deposit_funds_data(Some(5), Some(3));
    assert_eq!(data.len(), 19);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 501);
    assert_eq!(read_word(&market, 8321), 9);
    assert_eq!(read_word(&market, 8323), 5);
    // quote atoms = 5 * 3 = 15; base atoms = 3 * 2 = 6.
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1_015
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        5
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_006
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        4
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 13, 500, market_key, trader_key);
}

#[test]
fn official_raw_deposit_funds_zero_zero_is_header_only() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 510);
    write_word(&mut market, 8321, 4);
    write_word(&mut market, 8323, 2);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_deposit_funds_data(Some(0), Some(0))),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 511);
    assert_eq!(read_word(&market, 8321), 4);
    assert_eq!(read_word(&market, 8323), 2);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1_000
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 13, 510, market_key, trader_key);
}

#[test]



fn official_raw_deposit_funds_none_none_deposits_all_token_lots() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 515);
    write_word(&mut market, 8321, 4);
    write_word(&mut market, 8323, 2);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let data = raw_deposit_funds_data(None, None);
    assert_eq!(data.len(), 3);
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&data),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 516);
    // quote: floor(20/3)=6 lots; base: floor(10/2)=5 lots.
    assert_eq!(read_word(&market, 8321), 10);
    assert_eq!(read_word(&market, 8323), 7);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1_018
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        2
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_010
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        0
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 13, 515, market_key, trader_key);
}

#[test]
fn official_raw_deposit_funds_rejects_token_underflow_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 1);
    write_word(&mut market, 105, 1);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 520);
    write_word(&mut market, 8321, 0);
    write_word(&mut market, 8323, 0);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    // Trader quote starts at 20 atoms → 20/3 = 6 lots max; request 7 lots.
    assert_raw_reduce_token_rejected(&fixture, fixture.instruction(&raw_deposit_funds_data(Some(7), Some(0))));
}

#[test]
fn official_raw_cancel_by_id_rejects_noncanonical_wire_and_invalid_side_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 280);
    let before = market.data.clone();
    for data in [
        // length=9 exceeds profile capacity 8 / maxDataLen 141 for tag 10.
        {
            let mut over = vec![10, 9, 0, 0, 0];
            for i in 1u64..=9u64 {
                over.push(0u8);
                over.extend_from_slice(&i.to_le_bytes());
                over.extend_from_slice(&(!i).to_le_bytes());
            }
            over
        },
        // length=9 exceeds profile capacity 8 / maxDataLen 141.
        {
            let mut over = vec![11, 9, 0, 0, 0];
            for i in 1u64..=9u64 {
                over.push(0u8);
                over.extend_from_slice(&i.to_le_bytes());
                over.extend_from_slice(&( !i ).to_le_bytes());
            }
            over
        },
        // Truncated single-order payload.
        {
            let mut short = vec![11, 1, 0, 0, 0, 0];
            short.extend_from_slice(&5u64.to_le_bytes());
            short
        },
        // Trailing bytes after empty vec.
        vec![11, 0, 0, 0, 0, 0],
        // Invalid side.
        raw_cancel_by_id_data(11, &[(2, 5, !1u64)]),
    ] {
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_reduce_instruction(
            &data,
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_reduce_accounts(
                PHOENIX_PROGRAM,
                log_key,
                market_key,
                market.clone(),
                trader_key,
            ),
        );
        assert!(result.raw_result.is_err());
        assert_eq!(resulting_account(&result, &market_key).data, before);
        assert!(phoenix_data_payloads(&mollusk).is_empty());
    }
}

#[test]
fn official_raw_cancel_by_id_rejects_malformed_storage_and_token_context_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 290);
    write_word(&mut market, 8320, 5);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, !1u64, 1, 1, 0, 0],
        &[Check::success()],
    );
    write_word(&mut market, 115, 1);
    let before = market.data.clone();
    let (mollusk, log_key) = raw_reduce_harness();
    let data = raw_cancel_by_id_data(11, &[(0, 5, !1u64)]);
    let instruction = raw_reduce_instruction(
        &data,
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
    );
    assert!(result.raw_result.is_err());
    assert_eq!(resulting_account(&result, &market_key).data, before);
    assert!(phoenix_data_payloads(&mollusk).is_empty());

    let token_market_key = Pubkey::new_unique();
    let mut token_market = market_with_signer_trader();
    write_word(&mut token_market, MARKET_SEQUENCE_WORD, 291);
    let mut fixture = RawReduceTokenFixture::new(token_market_key, trader_key, token_market);
    write_word(&mut fixture.market, 1, 0);
    assert_raw_reduce_token_rejected(
        &fixture,
        fixture.instruction(&raw_cancel_by_id_data(10, &[(0, 5, !1u64)])),
    );
}

#[test]
fn official_raw_reduce_ask_has_no_tag4_status_gate_and_emits_exact_records() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    // The official tag-5 path skips CancelOrWithdrawContext::load and therefore does not call
    // assert_reduce_allowed. Tag 4 independently retains that status gate.
    write_word(&mut market, 1, 0);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 70);
    write_word(&mut market, 8322, 10);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, 11, 1, 10, 0, 0],
        &[Check::success()],
    );
    assert_eq!(&market.data[8316 * 8..8316 * 8 + 32], trader_key.as_ref());

    for (requested, removed, remaining, market_sequence) in
        [(0u64, 0u64, 10u64, 70u64), (4, 4, 6, 71), (100, 6, 0, 72)]
    {
        let (mollusk, log_key) = raw_reduce_harness();
        let instruction = raw_reduce_instruction(
            &raw_reduce_data(1, 7, 11, requested),
            PHOENIX_PROGRAM,
            log_key,
            false,
            market_key,
            true,
            trader_key,
            true,
            false,
        );
        let result = mollusk.process_and_validate_instruction(
            &instruction,
            &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
            &[Check::success(), Check::return_data(&removed.to_le_bytes())],
        );
        market = resulting_account(&result, &market_key);
        assert_eq!(
            read_word(&market, MARKET_SEQUENCE_WORD),
            market_sequence + 1
        );
        assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
        if remaining != 0 {
            assert_eq!(read_word(&market, 4219), remaining);
        }
        let payloads = phoenix_data_payloads(&mollusk);
        assert_eq!(payloads.len(), 1);
        assert_reduce_record(
            &payloads[0],
            5,
            market_sequence,
            market_key,
            trader_key,
            11,
            7,
            removed,
            remaining,
        );
    }
    assert_eq!(read_word(&market, ASK_TREE_WORD + 2), 0);
    assert_eq!(read_word(&market, 8322), 0);
    assert_eq!(read_word(&market, 8323), 10);
}

#[test]
fn official_raw_reduce_bid_uses_quote_collateral_and_canonical_event() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence = !12u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 3);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 90);
    write_word(&mut market, 8320, 100);
    write_word(&mut market, 8321, 7);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence, 1, 10, 0, 0],
        &[Check::success()],
    );

    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_reduce_data(0, 5, sequence, 4),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    );
    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 91);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, 119), 6);
    assert_eq!(read_word(&market, 8320), 70);
    assert_eq!(read_word(&market, 8321), 37);
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_record(
        &payloads[0],
        5,
        90,
        market_key,
        trader_key,
        sequence,
        5,
        4,
        6,
    );
}

#[test]
fn official_raw_reduce_missing_order_emits_header_and_advances_sequence() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 99);
    let (mollusk, log_key) = raw_reduce_harness();
    let instruction = raw_reduce_instruction(
        &raw_reduce_data(1, 77, 123, 9),
        PHOENIX_PROGRAM,
        log_key,
        false,
        market_key,
        true,
        trader_key,
        true,
        false,
    );
    let result = mollusk.process_and_validate_instruction(
        &instruction,
        &raw_reduce_accounts(PHOENIX_PROGRAM, log_key, market_key, market, trader_key),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    assert_eq!(
        read_word(
            &resulting_account(&result, &market_key),
            MARKET_SEQUENCE_WORD
        ),
        100
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 5, 99, market_key, trader_key);
}

#[test]
fn official_raw_reduce_rejects_malformed_adapter_inputs_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut canonical_market = market_with_signer_trader();
    write_word(&mut canonical_market, MARKET_SEQUENCE_WORD, 44);
    let (canonical_log, _) = Pubkey::find_program_address(&[b"log"], &PHOENIX_PROGRAM);
    let canonical_data = raw_reduce_data(1, 77, 123, 9);

    let assert_rejected = |data: Vec<u8>,
                           program_account: Pubkey,
                           log_key: Pubkey,
                           log_writable: bool,
                           market: Account,
                           market_writable: bool,
                           signer: bool,
                           trader_writable: bool| {
        let (mollusk, _) = raw_reduce_harness();
        let before = market.data.clone();
        let instruction = raw_reduce_instruction(
            &data,
            program_account,
            log_key,
            log_writable,
            market_key,
            market_writable,
            trader_key,
            signer,
            trader_writable,
        );
        let result = mollusk.process_instruction(
            &instruction,
            &raw_reduce_accounts(program_account, log_key, market_key, market, trader_key),
        );
        assert!(result.raw_result.is_err(), "malformed raw reduce succeeded");
        assert_eq!(resulting_account(&result, &market_key).data, before);
    };

    let mut wrong_side = canonical_data.clone();
    wrong_side[1] = 2;
    assert_rejected(
        wrong_side,
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market.clone(),
        true,
        true,
        false,
    );
    assert_rejected(
        canonical_data[..25].to_vec(),
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market.clone(),
        true,
        true,
        false,
    );
    assert_rejected(
        canonical_data.clone(),
        PHOENIX_PROGRAM,
        Pubkey::new_unique(),
        false,
        canonical_market.clone(),
        true,
        true,
        false,
    );
    assert_rejected(
        canonical_data.clone(),
        Pubkey::new_unique(),
        canonical_log,
        false,
        canonical_market.clone(),
        true,
        true,
        false,
    );
    assert_rejected(
        canonical_data.clone(),
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market.clone(),
        true,
        false,
        false,
    );
    assert_rejected(
        canonical_data.clone(),
        PHOENIX_PROGRAM,
        canonical_log,
        true,
        canonical_market.clone(),
        true,
        true,
        false,
    );
    assert_rejected(
        canonical_data.clone(),
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market.clone(),
        true,
        true,
        true,
    );
    assert_rejected(
        canonical_data.clone(),
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market.clone(),
        false,
        true,
        false,
    );
    canonical_market.owner = Pubkey::new_unique();
    assert_rejected(
        canonical_data,
        PHOENIX_PROGRAM,
        canonical_log,
        false,
        canonical_market,
        true,
        true,
        false,
    );
}

#[test]
fn official_raw_reduce_order_ask_withdraws_base_atoms_with_vault_pda() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 140);
    write_word(&mut market, 8322, 10);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, 11, 1, 10, 0, 0],
        &[Check::success()],
    );
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_reduce_withdraw_data(1, 7, 11, 4)),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    );

    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 141);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, 4219), 6);
    assert_eq!(read_word(&market, 8322), 6);
    assert_eq!(read_word(&market, 8323), 0);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        992
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        18
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        1_000
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_record(&payloads[0], 4, 140, market_key, trader_key, 11, 7, 4, 6);
}

#[test]
fn official_raw_reduce_order_bid_withdraws_quote_atoms_with_vault_pda() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let sequence = !12u64;
    let mut market = market_with_signer_trader();
    write_word(&mut market, 104, 2);
    write_word(&mut market, 105, 3);
    write_word(&mut market, MARKET_SEQUENCE_WORD, 160);
    write_word(&mut market, 8320, 100);
    write_word(&mut market, 8321, 7);
    market = run_market_write(
        "insertBid512",
        market,
        true,
        &[5, sequence, 1, 10, 0, 0],
        &[Check::success()],
    );
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_reduce_withdraw_data(0, 5, sequence, 4)),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&4u64.to_le_bytes())],
    );

    let market = resulting_account(&result, &market_key);
    assert_eq!(read_word(&market, MARKET_SEQUENCE_WORD), 161);
    assert_eq!(read_word(&market, ORDER_SEQUENCE_WORD), 1);
    assert_eq!(read_word(&market, 119), 6);
    assert_eq!(read_word(&market, 8320), 70);
    assert_eq!(read_word(&market, 8321), 7);
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.quote_vault_key)),
        910
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_quote_key)),
        110
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_record(
        &payloads[0],
        4,
        160,
        market_key,
        trader_key,
        sequence,
        5,
        4,
        6,
    );
}

#[test]
fn official_raw_reduce_order_missing_order_emits_header_without_token_transfer() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 180);
    let fixture = RawReduceTokenFixture::new(market_key, trader_key, market);
    let (mollusk, _) = raw_reduce_harness();
    let result = mollusk.process_and_validate_instruction(
        &fixture.instruction(&raw_reduce_withdraw_data(1, 77, 123, 9)),
        &fixture.accounts(),
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    assert_eq!(
        read_word(
            &resulting_account(&result, &market_key),
            MARKET_SEQUENCE_WORD
        ),
        181
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.base_vault_key)),
        1_000
    );
    assert_eq!(
        token_amount(&resulting_account(&result, &fixture.trader_base_key)),
        10
    );
    let payloads = phoenix_data_payloads(&mollusk);
    assert_eq!(payloads.len(), 1);
    assert_reduce_header(&payloads[0], 4, 180, market_key, trader_key);
}

#[test]
fn official_raw_reduce_order_rejects_invalid_token_context_atomically() {
    let trader_key = common::dummy_state_key(&PHOENIX_PROGRAM);
    let market_key = Pubkey::new_unique();
    let mut market = market_with_signer_trader();
    write_word(&mut market, MARKET_SEQUENCE_WORD, 200);
    write_word(&mut market, 8322, 10);
    market = run_market_write(
        "insertAsk512",
        market,
        true,
        &[7, 11, 1, 10, 0, 0],
        &[Check::success()],
    );
    let canonical = RawReduceTokenFixture::new(market_key, trader_key, market);
    let data = raw_reduce_withdraw_data(1, 7, 11, 4);

    let mut invalid_status = canonical.clone();
    write_word(&mut invalid_status.market, 1, 0);
    assert_raw_reduce_token_rejected(&invalid_status, invalid_status.instruction(&data));

    let mut wrong_program = canonical.clone();
    wrong_program.token_program_key = Pubkey::new_unique();
    assert_raw_reduce_token_rejected(&wrong_program, wrong_program.instruction(&data));

    let mut wrong_mint = canonical.clone();
    wrong_mint.trader_base = token_account(Pubkey::new_unique(), trader_key, 10);
    assert_raw_reduce_token_rejected(&wrong_mint, wrong_mint.instruction(&data));

    let mut wrong_authority = canonical.clone();
    wrong_authority.trader_base =
        token_account(wrong_authority.base_mint_key, Pubkey::new_unique(), 10);
    assert_raw_reduce_token_rejected(&wrong_authority, wrong_authority.instruction(&data));

    let mut wrong_vault_key = canonical.clone();
    write_pubkey(&mut wrong_vault_key.market, 80, Pubkey::new_unique());
    assert_raw_reduce_token_rejected(&wrong_vault_key, wrong_vault_key.instruction(&data));

    let mut wrong_vault_authority = canonical.clone();
    wrong_vault_authority.base_vault = token_account(
        wrong_vault_authority.base_mint_key,
        Pubkey::new_unique(),
        1_000,
    );
    assert_raw_reduce_token_rejected(
        &wrong_vault_authority,
        wrong_vault_authority.instruction(&data),
    );

    let mut readonly_token_account = canonical.instruction(&data);
    readonly_token_account.accounts[4].is_writable = false;
    assert_raw_reduce_token_rejected(&canonical, readonly_token_account);
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
        write_word(&mut market, MARKET_SEQUENCE_WORD, 777);
        write_word(&mut market, ORDER_SEQUENCE_WORD, 1);
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
fn trader_deposit_matches_official_sokoban_through_capacity() {
    assert_eq!(std::mem::size_of::<OfficialTraderTree>(), 18_464);
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let mut market = empty_small_market();
    let keys: Vec<[u64; 4]> = (0u64..128)
        .map(|index| [(index * 73) % 128, index << 8, 0, 0])
        .collect();

    for (index, key) in keys.iter().copied().enumerate() {
        let quote = 0x1000 + index as u64 * 11;
        let base = 0x2000 + index as u64 * 13;
        {
            let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official tree bytes");
            let mut trader_state = [0u64; 12];
            trader_state[1] = quote;
            trader_state[3] = base;
            assert_eq!(
                official.insert(key_words_bytes(key), trader_state),
                Some(index as u32 + 1)
            );
            assert!(official.is_valid_red_black_tree());
        }
        let mut args = key.to_vec();
        args.extend([quote, base]);
        market = run_market_write(
            "depositTrader128",
            market,
            true,
            &args,
            &[
                Check::success(),
                Check::return_data(&((index as u64) + 1).to_le_bytes()),
            ],
        );
        assert_trader_tree_bytes_eq(
            &market.data[8 * TRADER_TREE_WORD..],
            official_bytes.as_slice(),
            index * 2 + 1,
        );

        // Repeated deposits exercise get-without-allocation at every allocator size. Both free
        // balances change while locked/reserved words and topology stay byte-identical to Sokoban.
        let extra_quote = 3 + index as u64;
        let extra_base = 5 + index as u64;
        {
            let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official tree bytes");
            let address = official.get_addr(&key_words_bytes(key));
            assert_ne!(address, 0);
            let value = &mut official.get_node_mut(address).value;
            value[1] = value[1].checked_add(extra_quote).expect("quote free lots");
            value[3] = value[3].checked_add(extra_base).expect("base free lots");
            assert!(official.is_valid_red_black_tree());
        }
        let mut args = key.to_vec();
        args.extend([extra_quote, extra_base]);
        market = run_market_write(
            "depositTrader128",
            market,
            true,
            &args,
            &[
                Check::success(),
                Check::return_data(&((index as u64) + 1).to_le_bytes()),
            ],
        );
        assert_trader_tree_bytes_eq(
            &market.data[8 * TRADER_TREE_WORD..],
            official_bytes.as_slice(),
            index * 2 + 2,
        );
    }

    // Existing lookup precedes the capacity check. A genuinely absent trader still returns full.
    let existing = keys[37];
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        let address = official.get_addr(&key_words_bytes(existing));
        let value = &mut official.get_node_mut(address).value;
        value[1] += 17;
        value[3] += 19;
        assert!(official.is_valid_red_black_tree());
    }
    let mut existing_args = existing.to_vec();
    existing_args.extend([17, 19]);
    market = run_market_write(
        "depositTrader128",
        market,
        true,
        &existing_args,
        &[Check::success(), Check::return_data(&128u64.to_le_bytes())],
    );
    assert_trader_tree_bytes_eq(
        &market.data[8 * TRADER_TREE_WORD..],
        official_bytes.as_slice(),
        257,
    );
    let before_full = market.clone();
    let after_full = run_market_write(
        "depositTrader128",
        market,
        true,
        &[0xff, 0xff, 0, 0, 1, 1],
        &[Check::err(ProgramError::Custom(0x1003))],
    );
    assert_eq!(after_full.data, before_full.data);
}

#[test]
fn trader_deposit_overflow_and_invalid_accounts_are_atomic() {
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialTraderTree>()];
    OfficialTraderTree::new_from_slice(&mut official_bytes);
    let keys: Vec<[u64; 4]> = (1u64..=31).map(|index| [index * 7, 0, 0, 0]).collect();
    {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        for key in keys.iter().copied() {
            let mut trader_state = [0u64; 12];
            trader_state[1] = 100;
            trader_state[3] = 200;
            assert!(official
                .insert(key_words_bytes(key), trader_state)
                .is_some());
        }
    }
    let mut canonical = empty_small_market();
    install_official_trader_tree(&mut canonical, &official_bytes);
    let key = keys[12];
    let args = [key[0], key[1], key[2], key[3], 1, 1];

    let readonly = run_market_write(
        "depositTrader128",
        canonical.clone(),
        false,
        &args,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "depositTrader128",
        wrong_owner.clone(),
        true,
        &args,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let mut malformed = canonical.clone();
    write_word(&mut malformed, 8315, 127);
    let after_malformed = run_market_write(
        "depositTrader128",
        malformed.clone(),
        true,
        &args,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);

    let address = {
        let official = OfficialTraderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official tree bytes");
        official.get_addr(&key_words_bytes(key))
    } as usize;
    assert_ne!(address, 0);
    // Node words 7 and 9 are quote/base free. Either overflow must leave the whole account intact.
    let quote_free_word = TRADER_TREE_WORD + 4 + 7 + (address - 1) * 18;
    let mut quote_overflow = canonical.clone();
    write_word(&mut quote_overflow, quote_free_word, u64::MAX);
    let after_quote_overflow = run_market_write(
        "depositTrader128",
        quote_overflow.clone(),
        true,
        &args,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_quote_overflow.data, quote_overflow.data);

    // Quote succeeds in registers, but base overflow is discovered before the first store.
    let base_free_word = TRADER_TREE_WORD + 4 + 9 + (address - 1) * 18;
    let mut base_overflow = canonical;
    write_word(&mut base_overflow, base_free_word, u64::MAX);
    let after_base_overflow = run_market_write(
        "depositTrader128",
        base_overflow.clone(),
        true,
        &[key[0], key[1], key[2], key[3], 10, 1],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_base_overflow.data, base_overflow.data);
}

fn assert_order_insertion_matches_sokoban(method: &str, tree_word: usize, bid: bool) {
    assert_eq!(std::mem::size_of::<OfficialOrderTree>(), 32_800);
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialOrderTree>()];
    OfficialOrderTree::new_from_slice(&mut official_bytes);
    let mut market = empty_small_market();

    // The odd multipliers permute prices and raw sequence numbers. Filling every slot exercises
    // both rotation directions and every recursive red-uncle repair without any heap state.
    let orders: Vec<_> = (0u64..512)
        .map(|index| {
            let raw_sequence = ((index * 313) % 512) + 1;
            let sequence = if bid { !raw_sequence } else { raw_sequence };
            let key = OfficialOrderId {
                price_in_ticks: ((index * 257) % 97) + 1,
                order_sequence_number: sequence,
            };
            let value = [
                index + 11,
                (index + 1) * 17,
                50_000 + index,
                1_800_000_000 + index,
            ];
            (key, value)
        })
        .collect();

    for (index, (key, value)) in orders.iter().copied().enumerate() {
        {
            let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official order tree bytes");
            assert!(official.insert(key, value).is_some());
            assert!(official.is_valid_red_black_tree());
        }
        market = run_market_write(
            method,
            market,
            true,
            &[
                key.price_in_ticks,
                key.order_sequence_number,
                value[0],
                value[1],
                value[2],
                value[3],
            ],
            &[
                Check::success(),
                Check::return_data(&((index as u64) + 1).to_le_bytes()),
            ],
        );
        assert_order_tree_bytes_eq(
            &market,
            tree_word,
            official_bytes.as_slice(),
            if bid { "bid" } else { "ask" },
            index + 1,
        );
    }

    // Sokoban map semantics replace only the value for a duplicate key, including at capacity.
    let duplicate_key = orders[173].0;
    let replacement = [0x1111, 0x2222, 0x3333, 0x4444];
    {
        let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official order tree bytes");
        assert!(official.insert(duplicate_key, replacement).is_some());
        assert!(official.is_valid_red_black_tree());
    }
    market = run_market_write(
        method,
        market,
        true,
        &[
            duplicate_key.price_in_ticks,
            duplicate_key.order_sequence_number,
            replacement[0],
            replacement[1],
            replacement[2],
            replacement[3],
        ],
        &[Check::success(), Check::return_data(&512u64.to_le_bytes())],
    );
    assert_order_tree_bytes_eq(
        &market,
        tree_word,
        official_bytes.as_slice(),
        if bid { "bid" } else { "ask" },
        513,
    );

    let before_full = market.clone();
    let raw_sequence = 513;
    let full_sequence = if bid { !raw_sequence } else { raw_sequence };
    let after_full = run_market_write(
        method,
        market,
        true,
        &[101, full_sequence, 1, 2, 3, 4],
        &[Check::err(ProgramError::Custom(0x1003))],
    );
    assert_eq!(after_full.data, before_full.data);
}

#[test]
fn bid_insertion_matches_official_sokoban_through_capacity() {
    assert_order_insertion_matches_sokoban("insertBid512", BID_TREE_WORD, true);
}

#[test]
fn ask_insertion_matches_official_sokoban_through_capacity() {
    assert_order_insertion_matches_sokoban("insertAsk512", ASK_TREE_WORD, false);
}

fn full_official_order_tree(bid: bool) -> (Vec<u8>, Vec<(OfficialOrderId, [u64; 4])>) {
    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialOrderTree>()];
    OfficialOrderTree::new_from_slice(&mut official_bytes);
    let orders: Vec<_> = (0u64..512)
        .map(|index| {
            let raw_sequence = ((index * 313) % 512) + 1;
            let sequence = if bid { !raw_sequence } else { raw_sequence };
            (
                OfficialOrderId {
                    price_in_ticks: ((index * 257) % 97) + 1,
                    order_sequence_number: sequence,
                },
                [
                    index + 11,
                    (index + 1) * 17,
                    50_000 + index,
                    1_800_000_000 + index,
                ],
            )
        })
        .collect();
    {
        let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official order tree bytes");
        for (key, value) in orders.iter().copied() {
            assert!(official.insert(key, value).is_some());
        }
        assert!(official.is_valid_red_black_tree());
    }
    (official_bytes, orders)
}

fn assert_order_removal_matches_sokoban(
    remove_method: &str,
    insert_method: &str,
    tree_valid_method: &str,
    tree_word: usize,
    bid: bool,
) {
    let (mut official_bytes, orders) = full_official_order_tree(bid);
    let mut market = empty_small_market();
    install_official_order_tree(&mut market, tree_word, &official_bytes);

    // Independent odd permutation of insertion positions exercises leaf, one-child, two-child,
    // predecessor-transplant, and all delete-fixup cases against the official Sokoban bytes.
    for step in 0..512 {
        let key = orders[(step * 197) % 512].0;
        {
            let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official order tree bytes");
            assert!(official.remove(&key).is_some());
            assert!(official.is_valid_red_black_tree());
        }
        let remaining = 511 - step;
        market = run_market_write(
            remove_method,
            market,
            true,
            &[key.price_in_ticks, key.order_sequence_number],
            &[
                Check::success(),
                Check::return_data(&(remaining as u64).to_le_bytes()),
            ],
        );
        assert_order_tree_bytes_eq(
            &market,
            tree_word,
            &official_bytes,
            if bid { "bid remove" } else { "ask remove" },
            step + 1,
        );
    }
    run_view(
        tree_valid_method,
        market.clone(),
        &[Check::success(), Check::return_data(&1u64.to_le_bytes())],
    );

    let empty = market.clone();
    let missing_key = orders[0].0;
    let missing = run_market_write(
        remove_method,
        market.clone(),
        true,
        &[
            missing_key.price_in_ticks,
            missing_key.order_sequence_number,
        ],
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(missing.data, empty.data);

    // Exact bytes prove deletion's account-resident free-list is LIFO and insertion fully
    // reinitializes each reused fixed slot without retaining a detached or heap-backed node.
    for index in 0u64..16 {
        let raw_sequence = 1_000 + index;
        let key = OfficialOrderId {
            price_in_ticks: 200 + ((index * 11) % 17),
            order_sequence_number: if bid { !raw_sequence } else { raw_sequence },
        };
        let value = [index + 1, index + 101, index + 201, index + 301];
        {
            let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
                .expect("aligned official order tree bytes");
            assert!(official.insert(key, value).is_some());
            assert!(official.is_valid_red_black_tree());
        }
        market = run_market_write(
            insert_method,
            market,
            true,
            &[
                key.price_in_ticks,
                key.order_sequence_number,
                value[0],
                value[1],
                value[2],
                value[3],
            ],
            &[
                Check::success(),
                Check::return_data(&(index + 1).to_le_bytes()),
            ],
        );
        assert_order_tree_bytes_eq(
            &market,
            tree_word,
            &official_bytes,
            if bid { "bid reuse" } else { "ask reuse" },
            513 + index as usize,
        );
    }
}

#[test]
fn bid_removal_matches_official_sokoban_through_empty_and_reuse() {
    assert_order_removal_matches_sokoban(
        "removeBid512",
        "insertBid512",
        "bidTreeValid",
        BID_TREE_WORD,
        true,
    );
}

#[test]
fn ask_removal_matches_official_sokoban_through_empty_and_reuse() {
    assert_order_removal_matches_sokoban(
        "removeAsk512",
        "insertAsk512",
        "askTreeValid",
        ASK_TREE_WORD,
        false,
    );
}

#[test]
fn order_insertion_rejects_noncanonical_inputs_atomically() {
    let fresh = empty_small_market();
    for (method, wrong_sequence) in [("insertBid512", 1), ("insertAsk512", !1u64)] {
        let after_wrong_side = run_market_write(
            method,
            fresh.clone(),
            true,
            &[100, wrong_sequence, 1, 2, 3, 4],
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(after_wrong_side.data, fresh.data);
    }

    let mut official_bytes = vec![0u8; std::mem::size_of::<OfficialOrderTree>()];
    OfficialOrderTree::new_from_slice(&mut official_bytes);
    {
        let official = OfficialOrderTree::load_mut_bytes(&mut official_bytes)
            .expect("aligned official order tree bytes");
        for index in 1u64..=15 {
            assert!(official
                .insert(
                    OfficialOrderId {
                        price_in_ticks: (index * 7) % 17,
                        order_sequence_number: !index,
                    },
                    [index, index + 1, index + 2, index + 3],
                )
                .is_some());
        }
        assert!(official.is_valid_red_black_tree());
    }
    let mut canonical = empty_small_market();
    install_official_order_tree(&mut canonical, BID_TREE_WORD, &official_bytes);
    let valid_args = [200, !20u64, 21, 22, 23, 24];

    let after_readonly = run_market_write(
        "insertBid512",
        canonical.clone(),
        false,
        &valid_args,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_readonly.data, canonical.data);

    let mut wrong_owner = canonical.clone();
    wrong_owner.owner = Pubkey::new_unique();
    let after_wrong_owner = run_market_write(
        "insertBid512",
        wrong_owner.clone(),
        true,
        &valid_args,
        &[Check::err(ProgramError::Custom(1))],
    );
    assert_eq!(after_wrong_owner.data, wrong_owner.data);

    let root = read_word(&canonical, BID_TREE_WORD) as usize;
    let mut malformed = canonical;
    write_word(
        &mut malformed,
        BID_TREE_WORD + 5 + (root - 1) * 8,
        root as u64,
    );
    let after_malformed = run_market_write(
        "insertBid512",
        malformed.clone(),
        true,
        &valid_args,
        &[Check::err(ProgramError::Custom(0x1001))],
    );
    assert_eq!(after_malformed.data, malformed.data);
}

#[test]
fn order_removal_rejects_missing_and_noncanonical_inputs_atomically() {
    for (method, tree_word, bid) in [
        ("removeBid512", BID_TREE_WORD, true),
        ("removeAsk512", ASK_TREE_WORD, false),
    ] {
        let (official_bytes, orders) = full_official_order_tree(bid);
        let mut canonical = empty_small_market();
        install_official_order_tree(&mut canonical, tree_word, &official_bytes);
        let key = orders[173].0;

        let missing_sequence = if bid { !2_000u64 } else { 2_000u64 };
        let missing = run_market_write(
            method,
            canonical.clone(),
            true,
            &[10_000, missing_sequence],
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(missing.data, canonical.data);

        let wrong_side_sequence = if bid { 1 } else { !1u64 };
        let wrong_side = run_market_write(
            method,
            canonical.clone(),
            true,
            &[key.price_in_ticks, wrong_side_sequence],
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(wrong_side.data, canonical.data);

        let readonly = run_market_write(
            method,
            canonical.clone(),
            false,
            &[key.price_in_ticks, key.order_sequence_number],
            &[Check::err(ProgramError::Custom(1))],
        );
        assert_eq!(readonly.data, canonical.data);

        let mut wrong_owner = canonical.clone();
        wrong_owner.owner = Pubkey::new_unique();
        let after_wrong_owner = run_market_write(
            method,
            wrong_owner.clone(),
            true,
            &[key.price_in_ticks, key.order_sequence_number],
            &[Check::err(ProgramError::Custom(1))],
        );
        assert_eq!(after_wrong_owner.data, wrong_owner.data);

        let root = read_word(&canonical, tree_word) as usize;
        let mut malformed = canonical;
        write_word(&mut malformed, tree_word + 5 + (root - 1) * 8, root as u64);
        let after_malformed = run_market_write(
            method,
            malformed.clone(),
            true,
            &[key.price_in_ticks, key.order_sequence_number],
            &[Check::err(ProgramError::Custom(0x1001))],
        );
        assert_eq!(after_malformed.data, malformed.data);
    }
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
