use {
    mollusk_svm::{result::Check, Mollusk},
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::error::InstructionError,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf, process::Command},
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

fn call_so() -> PathBuf {
    PathBuf::from(env::var("SOLANA_LEAN_CALL_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/Call.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn stub_so() -> PathBuf {
    let dir = PathBuf::from(env::temp_dir()).join("solana-lean-call-stub");
    let src = dir.join("src/Stub/Stub.s");
    let deploy = dir.join("deploy");
    fs::create_dir_all(src.parent().unwrap()).unwrap();
    fs::create_dir_all(&deploy).unwrap();
    fs::write(
        &src,
        r#".globl entrypoint
entrypoint:
  lddw r0, 0
  exit
"#,
    )
    .unwrap();
    let status = Command::new("sbpf")
        .args(["build", "-d", deploy.to_str().unwrap()])
        .current_dir(&dir)
        .status()
        .expect("sbpf");
    assert!(status.success(), "sbpf stub failed");
    let so = deploy.join("Stub.so");
    assert!(so.exists(), "missing Stub.so");
    so
}

fn harness() -> (Pubkey, Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let callee_id = Pubkey::new_unique();
    let elf = fs::read(call_so()).unwrap_or_else(|e| panic!("read Call.so: {e}"));
    let stub = fs::read(stub_so()).unwrap_or_else(|e| panic!("read Stub.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    mollusk.add_program_with_loader_and_elf(
        &callee_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &stub,
    );
    (program_id, callee_id, mollusk)
}

fn funded(owner: &Pubkey) -> Account {
    Account::new(BASE_LAMPORTS, 0, owner)
}

#[test]
fn call_invokes_account_1() {
    let (program_id, callee_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let disc = instruction_discriminator("call", 0);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(callee_id, false),
        ],
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(&program_id)),
            (
                callee_id,
                mollusk_svm::program::create_program_account_loader_v3(&callee_id),
            ),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
        ],
    );
}

#[test]
fn call_wrong_program_fails() {
    let (program_id, _callee_id, mollusk) = harness();
    let payer = Pubkey::new_unique();
    let fake = Pubkey::new_unique();
    let disc = instruction_discriminator("call", 0);
    let ix = Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(fake, false),
        ],
    );
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (payer, funded(&program_id)),
            (fake, funded(&Pubkey::new_unique())),
        ],
        &[Check::instruction_err(InstructionError::UnsupportedProgramId)],
    );
}
