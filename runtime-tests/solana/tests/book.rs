mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::result::Check,
    solana_pubkey::Pubkey,
};

#[test]
fn bounded_loop_and_dynamic_index_run_on_chain() {
    let (program_id, mollusk) = harness("Book", "PF_BOOK_SO");
    let state_key = Pubkey::new_unique();
    let init = instruction(program_id, state_key, "initialize", &[7], true, true, vec![]);
    let initialized = mollusk.process_and_validate_instruction(
        &init,
        &[(state_key, state_account(&program_id, 40))],
        &[Check::success()],
    );
    let account = initialized
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after initialize")
        .1;

    let set = instruction(program_id, state_key, "setAt", &[2, 9], true, false, vec![]);
    let set_result = mollusk.process_and_validate_instruction(
        &set,
        &[(state_key, account)],
        &[Check::success(), Check::return_data(&9u64.to_le_bytes())],
    );
    let account = set_result
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after setAt")
        .1;
    assert_eq!((slot(&account, 0), slot(&account, 2)), (7, 9));

    let fill = instruction(program_id, state_key, "fillFirst", &[3], true, false, vec![]);
    let filled = mollusk.process_and_validate_instruction(
        &fill,
        &[(state_key, account)],
        &[Check::success(), Check::return_data(&3u64.to_le_bytes())],
    );
    let account = filled
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after fillFirst")
        .1;
    assert_eq!(
        (slot(&account, 0), slot(&account, 1), slot(&account, 2)),
        (7, 3, 9)
    );
}
