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
        let market = market_account(
            PHOENIX_PROGRAM,
            expected,
            MARKET_HEADER_DISCRIMINANT,
            bids,
            asks,
            seats,
        );
        run_view(
            "profileAccountBytes",
            market,
            &[
                Check::success(),
                Check::return_data(&(expected as u64).to_le_bytes()),
            ],
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
