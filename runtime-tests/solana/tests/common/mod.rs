#![allow(dead_code)]

use {
    mollusk_svm::Mollusk,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const LAYOUT_DOMAIN: &str = "proof-forge-solana-layout-v1:";
const BASE_LAMPORTS: u64 = 10 * LAMPORTS_PER_SOL;

pub fn instruction_discriminator(name: &str, param_count: usize) -> [u8; 8] {
    let params = vec!["u64"; param_count].join(",");
    let preimage = format!("{DISCRIMINATOR_DOMAIN}{name}({params})");
    Sha256::digest(preimage.as_bytes())[..8]
        .try_into()
        .expect("8-byte discriminator")
}

pub fn instruction(
    program_id: Pubkey,
    state_key: Pubkey,
    name: &str,
    params: &[u64],
    writable: bool,
    state_signer: bool,
    extra_accounts: Vec<AccountMeta>,
) -> Instruction {
    let mut data = instruction_discriminator(name, params.len()).to_vec();
    for param in params {
        data.extend_from_slice(&param.to_le_bytes());
    }
    let state_meta = if writable {
        AccountMeta::new(state_key, state_signer)
    } else {
        AccountMeta::new_readonly(state_key, state_signer)
    };
    let mut accounts = vec![state_meta];
    accounts.extend(extra_accounts);
    Instruction::new_with_bytes(program_id, &data, accounts)
}

pub fn harness(name: &str, env_name: &str) -> (Pubkey, Mollusk) {
    harness_at(name, env_name, Pubkey::new_unique())
}

pub fn harness_at(name: &str, env_name: &str, program_id: Pubkey) -> (Pubkey, Mollusk) {
    let path = PathBuf::from(env::var(env_name).unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/{name}.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }));
    let elf = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    (program_id, mollusk)
}

pub fn state_account(program_id: &Pubkey, data_len: usize) -> Account {
    Account::new(BASE_LAMPORTS, data_len, program_id)
}

pub fn dummy_state_key(program_id: &Pubkey) -> Pubkey {
    Pubkey::new_from_array(Sha256::digest(program_id.as_ref()).into())
}

pub fn dummy_state_account(program_id: &Pubkey) -> Account {
    let layout = "1|0:dummy:0:8:8:u64-le";
    let digest = Sha256::digest(format!("{LAYOUT_DOMAIN}{layout}").as_bytes());
    let marker = u64::from_be_bytes(digest[..8].try_into().expect("layout marker"));
    let mut account = state_account(program_id, 16);
    account.data[..8].copy_from_slice(&marker.to_le_bytes());
    account
}

pub fn plain_account() -> Account {
    Account::new(BASE_LAMPORTS, 0, &Pubkey::new_unique())
}

pub fn slot(account: &Account, index: usize) -> u64 {
    let offset = 8 + index * 8;
    u64::from_le_bytes(
        account.data[offset..offset + 8]
            .try_into()
            .expect("u64 state slot"),
    )
}
