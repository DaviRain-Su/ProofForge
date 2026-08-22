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
const XFER: u64 = 1_000_000;

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
    PathBuf::from(env::var("SOLANA_LEAN_TRANSFER_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Transfer.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Transfer.so: {e}"));
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
    payer: Pubkey,
    recipient: Pubkey,
    system: Pubkey,
    disc_hex: &str,
    params: &[u64],
    payer_signer: bool,
) -> Instruction {
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(disc_hex, params),
        vec![
            AccountMeta::new(payer, payer_signer),
            AccountMeta::new(recipient, false),
            AccountMeta::new_readonly(system, false),
        ],
    )
}

#[test]
fn transfer_moves_lamports_and_returns() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let recipient = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let disc = instruction_discriminator("transfer", 1);
    let ix = build_ix(program_id, payer, recipient, system, &disc, &[XFER], true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(BASE_LAMPORTS)),
            (recipient, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&XFER.to_le_bytes()),
            Check::account(&payer)
                .lamports(BASE_LAMPORTS - XFER)
                .build(),
            Check::account(&recipient).lamports(XFER).build(),
        ],
    );
}

#[test]
fn transfer_missing_payer_signer_fails() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let recipient = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let disc = instruction_discriminator("transfer", 1);
    let ix = build_ix(program_id, payer, recipient, system, &disc, &[XFER], false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(BASE_LAMPORTS)),
            (recipient, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&payer).lamports(BASE_LAMPORTS).build(),
            Check::account(&recipient).lamports(0).build(),
        ],
    );
}

#[test]
fn transfer_underfunded_rolls_back() {
    let (program_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let recipient = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let disc = instruction_discriminator("transfer", 1);
    let ix = build_ix(program_id, payer, recipient, system, &disc, &[XFER], true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(XFER - 1)),
            (recipient, funded(0)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&payer).lamports(XFER - 1).build(),
            Check::account(&recipient).lamports(0).build(),
        ],
    );
}
