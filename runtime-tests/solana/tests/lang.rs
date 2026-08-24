mod common;

use {
    common::{harness, instruction, state_account},
    mollusk_svm::result::Check,
    solana_pubkey::Pubkey,
};

#[test]
fn bitwise_shift_and_fold_semantics_run_on_chain() {
    let (program_id, mollusk) = harness("Lang", "PF_LANG_SO");
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

    let shift = instruction(program_id, state_key, "shl", &[1, 65], false, false, vec![]);
    mollusk.process_and_validate_instruction(
        &shift,
        &[(state_key, account.clone())],
        &[Check::success(), Check::return_data(&2u64.to_le_bytes())],
    );

    let band = instruction(
        program_id,
        state_key,
        "band",
        &[0xf0, 0x0f],
        false,
        false,
        vec![],
    );
    mollusk.process_and_validate_instruction(
        &band,
        &[(state_key, account.clone())],
        &[Check::success(), Check::return_data(&0u64.to_le_bytes())],
    );

    let sum = instruction(program_id, state_key, "sum4", &[], false, false, vec![]);
    mollusk.process_and_validate_instruction(
        &sum,
        &[(state_key, account)],
        &[Check::success(), Check::return_data(&7u64.to_le_bytes())],
    );
}
