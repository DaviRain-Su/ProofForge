mod common;

use {
    common::{harness, instruction, slot, state_account},
    mollusk_svm::result::Check,
    solana_pubkey::Pubkey,
};

fn resulting_state(
    result: mollusk_svm::result::InstructionResult,
    state_key: &Pubkey,
) -> solana_account::Account {
    result
        .resulting_accounts
        .into_iter()
        .find(|(key, _)| key == state_key)
        .expect("resulting state")
        .1
}

#[test]
fn red_black_insertions_run_on_chain() {
    let (program_id, mollusk) = harness("Tree", "PF_TREE_SO");
    let state_key = Pubkey::new_unique();
    let init = instruction(program_id, state_key, "initialize", &[0], true, true, vec![]);
    let initialized = mollusk.process_and_validate_instruction(
        &init,
        &[(state_key, state_account(&program_id, 232))],
        &[Check::success()],
    );
    let mut account = resulting_state(initialized, &state_key);

    for (key, value, address) in [(30, 300, 1), (20, 200, 2), (10, 100, 3)] {
        let insert = instruction(
            program_id,
            state_key,
            "insertNode",
            &[key, value],
            true,
            false,
            vec![],
        );
        let inserted = mollusk.process_and_validate_instruction(
            &insert,
            &[(state_key, account)],
            &[
                Check::success(),
                Check::return_data(&(address as u64).to_le_bytes()),
            ],
        );
        account = resulting_state(inserted, &state_key);
    }

    assert_eq!(slot(&account, 0), 2, "root address");
    assert_eq!(slot(&account, 1), 3, "tree size");
    assert_eq!(slot(&account, 14), 20, "root key");
    assert_eq!(slot(&account, 10), 3, "root left child");
    assert_eq!(slot(&account, 11), 1, "root right child");
    assert_eq!(slot(&account, 13), 0, "root is black");
}
