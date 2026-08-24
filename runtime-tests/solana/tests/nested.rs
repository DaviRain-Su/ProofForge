mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::result::Check,
    solana_pubkey::Pubkey,
};

#[test]
fn nested_projection_updates_on_chain() {
    let (program_id, mollusk) = harness("Nested", "PF_NESTED_SO");
    let state_key = Pubkey::new_unique();
    let init = instruction(program_id, state_key, "initialize", &[100], true, true, vec![]);
    let initialized = mollusk.process_and_validate_instruction(
        &init,
        &[(state_key, state_account(&program_id, 32))],
        &[Check::success()],
    );
    let account = initialized
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after initialize")
        .1;
    assert_eq!((slot(&account, 0), slot(&account, 1)), (100, 0));

    let post = instruction(program_id, state_key, "postAsk", &[8], true, false, vec![]);
    let posted = mollusk.process_and_validate_instruction(
        &post,
        &[(state_key, account)],
        &[Check::success(), Check::return_data(&8u64.to_le_bytes())],
    );
    let account = posted
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after postAsk")
        .1;
    assert_eq!((slot(&account, 0), slot(&account, 1)), (100, 8));
}
