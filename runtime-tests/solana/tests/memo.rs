use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_memo::memo,
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
    PathBuf::from(env::var("PF_MEMO_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Memo.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read Memo.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    memo::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn funded() -> Account {
    Account::new(BASE_LAMPORTS, 0, &Pubkey::default())
}

fn build_ix(program_id: Pubkey, acc0: Pubkey, memo_id: Pubkey, acc0_signer: bool) -> Instruction {
    let disc = instruction_discriminator("write", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(acc0, acc0_signer),
            AccountMeta::new_readonly(memo_id, false),
        ],
    )
}

#[test]
fn memo_writes_ok() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (memo_id, memo_acc) = memo::keyed_account();
    let ix = build_ix(program_id, acc0, memo_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(acc0, funded()), (memo_id, memo_acc)],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
        ],
    );
}

#[test]
fn memo_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let acc0 = Pubkey::new_unique();
    let (memo_id, memo_acc) = memo::keyed_account();
    let ix = build_ix(program_id, acc0, memo_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[(acc0, funded()), (memo_id, memo_acc)],
        &[Check::err(ProgramError::Custom(1))],
    );
}
