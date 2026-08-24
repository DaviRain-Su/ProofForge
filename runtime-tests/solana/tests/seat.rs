mod common;

use {
    common::{harness, instruction, plain_account, state_account},
    mollusk_svm::result::Check,
    solana_instruction::AccountMeta,
    solana_pubkey::Pubkey,
};

#[test]
fn pda_view_runs_with_walk_prelude() {
    let (program_id, mollusk) = harness("Seat", "PF_SEAT_SO");
    let state_key = Pubkey::new_unique();
    let extras = [
        Pubkey::new_unique(),
        Pubkey::new_unique(),
        Pubkey::new_unique(),
        Pubkey::new_unique(),
    ];
    let init = instruction(
        program_id,
        state_key,
        "initialize",
        &[0],
        true,
        true,
        extras
            .iter()
            .map(|key| AccountMeta::new_readonly(*key, false))
            .collect(),
    );
    let mut accounts = vec![(state_key, state_account(&program_id, 16))];
    accounts.extend(extras.iter().map(|key| (*key, plain_account())));
    let initialized =
        mollusk.process_and_validate_instruction(&init, &accounts, &[Check::success()]);
    let state = initialized
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == &state_key)
        .expect("state after initialize")
        .1;

    let bump = Pubkey::find_program_address(&[b"vault"], &program_id).1 as u64;
    let get = instruction(
        program_id,
        state_key,
        "get",
        &[],
        false,
        false,
        extras
            .iter()
            .map(|key| AccountMeta::new_readonly(*key, false))
            .collect(),
    );
    let mut accounts = vec![(state_key, state)];
    accounts.extend(extras.iter().map(|key| (*key, plain_account())));
    mollusk.process_and_validate_instruction(
        &get,
        &accounts,
        &[Check::success(), Check::return_data(&bump.to_le_bytes())],
    );
}
