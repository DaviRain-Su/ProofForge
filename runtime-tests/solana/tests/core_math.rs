//! Cross-target shared UInt64 math, SVM half: min/max/overflow-safe average and checked ceil-div.

mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::result::Check,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

fn initialized() -> (Pubkey, MolluskFixture, solana_account::Account) {
    let (program_id, mollusk) = harness("BatchSizer", "PF_BATCH_SIZER_SO");
    let state_key = Pubkey::new_unique();
    let ix = instruction(
        program_id,
        state_key,
        "initialize",
        &[7],
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
    let (program_id, fixture, account) = initialized();
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
fn ceil_div_handles_maximum_and_rejects_zero_atomically() {
    let (program_id, fixture, account) = initialized();
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
