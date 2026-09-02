mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const SPACE: usize = 16;

fn instruction_discriminator(name: &str, param_count: usize) -> String {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    let digest = Sha256::digest(preimage.as_bytes());
    hex::encode(digest)[..16].to_string()
}

fn discriminator_bytes(hex16: &str) -> [u8; 8] {
    let raw = hex::decode(hex16).expect("hex");
    let mut out = [0u8; 8];
    out.copy_from_slice(&raw);
    out
}

fn instruction_data(disc_hex: &str, params: &[u64]) -> Vec<u8> {
    let mut data = discriminator_bytes(disc_hex).to_vec();
    for p in params {
        data.extend_from_slice(&p.to_le_bytes());
    }
    data
}

fn so_path() -> PathBuf {
    PathBuf::from(env::var("PF_SYSALLOC_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/SysAlloc.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read SysAlloc.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn system_program_keyed() -> (Pubkey, Account) {
    mollusk_svm::program::keyed_account_for_system_program()
}

fn build_ix(
    program_id: Pubkey,
    name: &str,
    acc0: Pubkey,
    system: Pubkey,
    acc0_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(common::dummy_state_key(&program_id), false),
            AccountMeta::new(acc0, acc0_signer),
            AccountMeta::new_readonly(system, false),
        ],
    )
}

#[test]
fn allocate_grows_system_account() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "alloc", acc0, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (acc0, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&16u64.to_le_bytes()),
            Check::account(&acc0)
                .space(SPACE)
                .owner(&Pubkey::default())
                .build(),
        ],
    );
}

#[test]
fn allocate_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "alloc", acc0, system, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (acc0, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&acc0).space(0).build(),
        ],
    );
}

#[test]
fn assign_sets_owner_to_program() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "assign", acc0, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (acc0, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&acc0).owner(&program_id).build(),
        ],
    );
}

#[test]
fn assign_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "assign", acc0, system, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (acc0, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&acc0).owner(&Pubkey::default()).build(),
        ],
    );
}

/// `svm-sdk-002`: System.assign must not silently re-point a foreign-owned account. Owner
/// reassignment of live program-owned accounts stays permanently unavailable; inbound assign is
/// system-owned → current program only.
#[test]
fn assign_foreign_owned_fails_closed() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let foreign = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "assign", acc0, system, true);
    let foreign_owned = Account::new(BASE_LAMPORTS, 0, &foreign);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (acc0, foreign_owned),
            (system, system_acc),
        ],
        &[
            Check::instruction_err(
                solana_instruction::error::InstructionError::ModifiedProgramId,
            ),
            Check::account(&acc0).owner(&foreign).lamports(BASE_LAMPORTS).build(),
        ],
    );
}
