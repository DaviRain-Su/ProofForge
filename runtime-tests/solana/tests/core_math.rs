//! Cross-target UInt64 math, SVM half: bounded helpers, saturation, and rounded integer math.

mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::result::Check,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

fn initialized(initial: u64) -> (Pubkey, MolluskFixture, solana_account::Account) {
    let (program_id, mollusk) = harness("BatchSizer", "PF_BATCH_SIZER_SO");
    let state_key = Pubkey::new_unique();
    let ix = instruction(
        program_id,
        state_key,
        "initialize",
        &[initial],
        true,
        true,
        vec![],
    );
    let result = mollusk.process_and_validate_instruction(
        &ix,
        &[(state_key, state_account(&program_id, 16))],
        &[Check::success()],
    );
    let account = result
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after initialize")
        .1;
    (program_id, MolluskFixture { mollusk, state_key }, account)
}

struct MolluskFixture {
    mollusk: mollusk_svm::Mollusk,
    state_key: Pubkey,
}

impl MolluskFixture {
    fn call(
        &self,
        program_id: Pubkey,
        account: solana_account::Account,
        name: &str,
        params: &[u64],
        writable: bool,
        checks: &[Check],
    ) -> mollusk_svm::result::InstructionResult {
        let ix = instruction(
            program_id,
            self.state_key,
            name,
            params,
            writable,
            false,
            vec![],
        );
        self.mollusk
            .process_and_validate_instruction(&ix, &[(self.state_key, account)], checks)
    }
}

#[test]
fn scalar_queries_preserve_unsigned_boundary_laws() {
    let (program_id, fixture, account) = initialized(7);
    fixture.call(
        program_id,
        account.clone(),
        "smaller",
        &[u64::MAX, 7],
        false,
        &[Check::success(), Check::return_data(&7u64.to_le_bytes())],
    );
    fixture.call(
        program_id,
        account.clone(),
        "larger",
        &[u64::MAX, 7],
        false,
        &[
            Check::success(),
            Check::return_data(&u64::MAX.to_le_bytes()),
        ],
    );
    fixture.call(
        program_id,
        account,
        "midpoint",
        &[0, u64::MAX],
        false,
        &[
            Check::success(),
            Check::return_data(&(u64::MAX / 2).to_le_bytes()),
        ],
    );
}

#[test]
fn integer_logs_cover_zero_powers_and_uint64_maximum() {
    let (program_id, fixture, account) = initialized(7);
    for (name, input, expected) in [
        ("binaryOrder", 0, 0u64),
        ("binaryOrder", 1, 0),
        ("binaryOrder", 2, 1),
        ("binaryOrder", u64::MAX, 63),
        ("decimalOrder", 9, 0),
        ("decimalOrder", 10, 1),
        ("decimalOrder", 10_000_000_000_000_000_000, 19),
        ("decimalOrder", u64::MAX, 19),
        ("byteOrder", 255, 0),
        ("byteOrder", 256, 1),
        ("byteOrder", u64::MAX, 7),
        ("binaryOrderUp", 1, 0),
        ("binaryOrderUp", 3, 2),
        ("binaryOrderUp", 4, 2),
        ("binaryOrderUp", u64::MAX, 64),
        ("decimalOrderUp", 9, 1),
        ("decimalOrderUp", 10, 1),
        ("decimalOrderUp", 11, 2),
        ("decimalOrderUp", u64::MAX, 20),
        ("byteOrderUp", 255, 1),
        ("byteOrderUp", 256, 1),
        ("byteOrderUp", 257, 2),
        ("byteOrderUp", u64::MAX, 8),
    ] {
        fixture.call(
            program_id,
            account.clone(),
            name,
            &[input],
            false,
            &[
                Check::success(),
                Check::return_data(&expected.to_le_bytes()),
            ],
        );
    }
}

#[test]
fn integer_square_root_covers_zero_squares_and_uint64_maximum() {
    let (program_id, fixture, account) = initialized(7);
    for (input, expected) in [
        (0, 0u64),
        (1, 1),
        (2, 1),
        (3, 1),
        (4, 2),
        (15, 3),
        (16, 4),
        (17, 4),
        (18_446_744_065_119_617_025, 4_294_967_295),
        (u64::MAX, 4_294_967_295),
    ] {
        fixture.call(
            program_id,
            account.clone(),
            "capacityRoot",
            &[input],
            false,
            &[
                Check::success(),
                Check::return_data(&expected.to_le_bytes()),
            ],
        );
    }

    for (input, expected) in [
        (0, 0u64),
        (1, 1),
        (2, 2),
        (3, 2),
        (4, 2),
        (15, 4),
        (16, 4),
        (17, 5),
        (18_446_744_065_119_617_025, 4_294_967_295),
        (18_446_744_065_119_617_026, 4_294_967_296),
        (u64::MAX, 4_294_967_296),
    ] {
        fixture.call(
            program_id,
            account.clone(),
            "capacityRootUp",
            &[input],
            false,
            &[
                Check::success(),
                Check::return_data(&expected.to_le_bytes()),
            ],
        );
    }
}

#[test]
fn ceil_div_handles_maximum_and_rejects_zero_atomically() {
    let (program_id, fixture, account) = initialized(7);
    let planned = fixture.call(
        program_id,
        account,
        "plan",
        &[u64::MAX, 2],
        true,
        &[
            Check::success(),
            Check::return_data(&(1u64 << 63).to_le_bytes()),
        ],
    );
    let account = planned
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &fixture.state_key)
        .expect("state after plan")
        .1;
    assert_eq!(slot(&account, 0), 1u64 << 63);

    let before_failure = account.data.clone();
    let failed = fixture.call(
        program_id,
        account,
        "plan",
        &[u64::MAX, 0],
        true,
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&fixture.state_key)
                .data(&before_failure)
                .build(),
        ],
    );
    let account = failed
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &fixture.state_key)
        .expect("state after rejected plan")
        .1;
    assert_eq!(account.data, before_failure);
}

#[test]
fn full_precision_mul_div_handles_wide_product_and_atomic_errors() {
    let (program_id, fixture, account) = initialized(7);
    let exact = fixture.call(
        program_id,
        account,
        "prorate",
        &[u64::MAX, 2, 2],
        true,
        &[
            Check::success(),
            Check::return_data(&u64::MAX.to_le_bytes()),
        ],
    );
    let account = exact
        .get_account(&fixture.state_key)
        .expect("state after full-precision ratio")
        .clone();
    assert_eq!(slot(&account, 0), u64::MAX);

    for (params, error) in [
        ([7, 9, 0], ProgramError::Custom(1)),
        ([1u64 << 63, 2, 1], ProgramError::Custom(1)),
    ] {
        let before = account.data.clone();
        let rejected = fixture.call(
            program_id,
            account.clone(),
            "prorate",
            &params,
            true,
            &[
                Check::err(error),
                Check::account(&fixture.state_key).data(&before).build(),
            ],
        );
        let rejected_account = rejected
            .get_account(&fixture.state_key)
            .expect("state after rejected full-precision ratio");
        assert_eq!(rejected_account.data, before);
    }
}

#[test]
fn saturating_mutations_clamp_both_bounds_and_preserve_exact_products() {
    let (program_id, fixture, account) = initialized(u64::MAX - 2);
    let reserved = fixture.call(
        program_id,
        account,
        "reserve",
        &[5],
        true,
        &[
            Check::success(),
            Check::return_data(&u64::MAX.to_le_bytes()),
        ],
    );
    let account = reserved
        .get_account(&fixture.state_key)
        .expect("state after reserve")
        .clone();
    assert_eq!(slot(&account, 0), u64::MAX);

    let consumed = fixture.call(
        program_id,
        account,
        "consume",
        &[u64::MAX],
        true,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let account = consumed
        .get_account(&fixture.state_key)
        .expect("state after consume")
        .clone();
    assert_eq!(slot(&account, 0), 0);

    let amplified_zero = fixture.call(
        program_id,
        account,
        "amplify",
        &[u64::MAX],
        true,
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );
    let account = amplified_zero
        .get_account(&fixture.state_key)
        .expect("state after zero amplify")
        .clone();
    assert_eq!(slot(&account, 0), 0);

    let reserved = fixture.call(
        program_id,
        account,
        "reserve",
        &[u64::MAX / 2 + 1],
        true,
        &[
            Check::success(),
            Check::return_data(&(u64::MAX / 2 + 1).to_le_bytes()),
        ],
    );
    let account = reserved
        .get_account(&fixture.state_key)
        .expect("state before amplify")
        .clone();
    let amplified = fixture.call(
        program_id,
        account,
        "amplify",
        &[2],
        true,
        &[
            Check::success(),
            Check::return_data(&u64::MAX.to_le_bytes()),
        ],
    );
    let account = amplified
        .get_account(&fixture.state_key)
        .expect("state after amplify");
    assert_eq!(slot(account, 0), u64::MAX);
}
