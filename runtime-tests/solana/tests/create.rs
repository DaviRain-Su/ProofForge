mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const CREATE_LAMPORTS: u64 = LAMPORTS_PER_SOL;
const SPACE: u64 = 16;

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
    PathBuf::from(env::var("PF_CREATE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Create.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Create.so: {e}"));
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
    params: &[u64],
    payer: Pubkey,
    new_acc: Pubkey,
    system: Pubkey,
    new_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator(name, params.len());
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, params),
        vec![
            AccountMeta::new(common::dummy_state_key(&program_id), false),
            AccountMeta::new(payer, true),
            AccountMeta::new(new_acc, new_signer),
            AccountMeta::new_readonly(system, false),
        ],
    )
}

#[test]
fn create_allocates_account_owned_by_program() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let new_acc = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "create", &[CREATE_LAMPORTS], payer, new_acc, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (payer, funded(BASE_LAMPORTS)),
            (new_acc, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&CREATE_LAMPORTS.to_le_bytes()),
            Check::account(&payer)
                .lamports(BASE_LAMPORTS - CREATE_LAMPORTS)
                .build(),
            Check::account(&new_acc)
                .lamports(CREATE_LAMPORTS)
                .owner(&program_id)
                .space(SPACE as usize)
                .build(),
        ],
    );
}

#[test]
fn create_rent_exempt_uses_current_sysvar_minimum() {
    let (program_id, mut mollusk) = harness();
    mollusk.sysvars.rent = Rent::with_lamports_per_byte(1234);
    let payer = Pubkey::new_unique();
    let new_acc = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let minimum = mollusk.sysvars.rent.minimum_balance(SPACE as usize);
    let ix = build_ix(program_id, "createRentExempt", &[], payer, new_acc, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (payer, funded(BASE_LAMPORTS)),
            (new_acc, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&payer)
                .lamports(BASE_LAMPORTS - minimum)
                .build(),
            Check::account(&new_acc)
                .lamports(minimum)
                .owner(&program_id)
                .space(SPACE as usize)
                .build(),
        ],
    );
}

#[test]
fn create_missing_new_account_signer_fails() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let new_acc = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "create", &[CREATE_LAMPORTS], payer, new_acc, system, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (common::dummy_state_key(&program_id), common::dummy_state_account(&program_id)),
            (payer, funded(BASE_LAMPORTS)),
            (new_acc, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&payer).lamports(BASE_LAMPORTS).build(),
            Check::account(&new_acc).lamports(0).build(),
        ],
    );
}
