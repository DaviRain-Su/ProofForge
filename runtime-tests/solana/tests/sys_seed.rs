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
const SEED: &str = "vault";

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
    PathBuf::from(env::var("SOLANA_LEAN_SYSSEED_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/SysSeed.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read SysSeed.so: {e}"));
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

fn derived(base: &Pubkey, owner: &Pubkey) -> Pubkey {
    Pubkey::create_with_seed(base, SEED, owner).expect("create_with_seed")
}

fn build_ix(
    program_id: Pubkey,
    base: Pubkey,
    derived_key: Pubkey,
    system: Pubkey,
    base_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("openSeed", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(base, base_signer),
            AccountMeta::new(derived_key, false),
            AccountMeta::new_readonly(system, false),
        ],
    )
}

#[test]
fn allocate_with_seed_grows_derived_account() {
    let (program_id, mollusk) = harness();
    let base = Pubkey::new_unique();
    let derived_key = derived(&base, &program_id);
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, base, derived_key, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (base, funded(BASE_LAMPORTS)),
            (derived_key, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::success(),
            Check::return_data(&16u64.to_le_bytes()),
            Check::account(&derived_key)
                .space(SPACE)
                .owner(&program_id)
                .build(),
        ],
    );
}

#[test]
fn allocate_with_seed_missing_signer_fails() {
    let (program_id, mollusk) = harness();
    let base = Pubkey::new_unique();
    let derived_key = derived(&base, &program_id);
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, base, derived_key, system, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (base, funded(BASE_LAMPORTS)),
            (derived_key, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            Check::err(ProgramError::Custom(1)),
            Check::account(&derived_key).space(0).build(),
        ],
    );
}

#[test]
fn allocate_with_seed_wrong_address_fails() {
    let (program_id, mollusk) = harness();
    let base = Pubkey::new_unique();
    let wrong = Pubkey::new_unique();
    let (system, system_acc) = system_program_keyed();
    let ix = build_ix(program_id, base, wrong, system, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (base, funded(BASE_LAMPORTS)),
            (wrong, funded(BASE_LAMPORTS)),
            (system, system_acc),
        ],
        &[
            // System AddressWithSeedMismatch = custom 5
            Check::err(ProgramError::Custom(5)),
            Check::account(&wrong).space(0).build(),
        ],
    );
}
