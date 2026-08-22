use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;
const CREATE_LAMPORTS: u64 = LAMPORTS_PER_SOL;
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
    PathBuf::from(env::var("PF_CREATEPDA_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/CreatePda.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Pubkey, u8, Mollusk) {
    let program_id = Pubkey::new_unique();
    let (pda, bump) = Pubkey::find_program_address(&[b"vault"], &program_id);
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read CreatePda.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, pda, bump, mollusk)
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
    payer: Pubkey,
    pda: Pubkey,
    system: Pubkey,
) -> Instruction {
    let disc = instruction_discriminator(name, 1);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[CREATE_LAMPORTS]),
        vec![
            AccountMeta::new(payer, true),
            AccountMeta::new(pda, false),
            AccountMeta::new_readonly(system, false),
        ],
    )
}

#[test]
fn create_pda_allocates_vault() {
    let (program_id, pda, bump, mollusk) = harness();
    assert!((1..=255).contains(&bump));
    let payer = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "openPda", payer, pda, system);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(BASE_LAMPORTS)),
            (pda, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&CREATE_LAMPORTS.to_le_bytes()),
            Check::account(&payer)
                .lamports(BASE_LAMPORTS - CREATE_LAMPORTS)
                .build(),
            Check::account(&pda)
                .lamports(CREATE_LAMPORTS)
                .owner(&program_id)
                .space(SPACE)
                .build(),
        ],
    );
}

#[test]
fn create_pda_wrong_bump_fails() {
    let (program_id, pda, _bump, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, "openBad", payer, pda, system);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(BASE_LAMPORTS)),
            (pda, funded(0)),
            (system, system_acc),
        ],
        &[Check::instruction_err(
            solana_instruction::error::InstructionError::ProgramFailedToComplete,
        )],
    );
}
