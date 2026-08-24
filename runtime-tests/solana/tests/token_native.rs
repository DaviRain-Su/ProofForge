mod common;

use {
    mollusk_svm::{result::Check, Mollusk},
    mollusk_svm_programs_token::token,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_instruction::{AccountMeta, Instruction},
    solana_native_token::LAMPORTS_PER_SOL,
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    spl_token_interface::{
        native_mint,
        state::{Account as TokenAccount, AccountState},
    },
    std::{env, fs, path::PathBuf},
};

const DISCRIMINATOR_DOMAIN: &str = "proof-forge-solana-v1:";
const EXTRA: u64 = 1_000_000;
const TOKEN_ACCOUNT_LEN: usize = 165;

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
    PathBuf::from(env::var("PF_TOKENNATIVE_SO").unwrap_or_else(|_| {
        format!(
            "{}/build/sbpf/TokenNative.so",
            env::var("CARGO_MANIFEST_DIR")
                .map(|p| format!("{p}/../.."))
                .unwrap_or_else(|_| ".".into())
        )
    }))
}

fn harness() -> (Pubkey, Mollusk) {
    let program_id = Pubkey::new_unique();
    let elf = fs::read(so_path()).unwrap_or_else(|e| panic!("read TokenNative.so: {e}"));
    let mut mollusk = Mollusk::default();
    mollusk.add_program_with_loader_and_elf(
        &program_id,
        &mollusk_svm::program::loader_keys::LOADER_V3,
        &elf,
    );
    token::add_program(&mut mollusk);
    (program_id, mollusk)
}

fn funded(lamports: u64) -> Account {
    Account::new(lamports, 0, &Pubkey::default())
}

fn native_token_account(owner: Pubkey, extra: u64) -> Account {
    let rent = Rent::default().minimum_balance(TOKEN_ACCOUNT_LEN);
    let mut acc = token::create_account_for_token_account(TokenAccount {
        mint: native_mint::ID,
        owner,
        amount: 0,
        delegate: None.into(),
        state: AccountState::Initialized,
        is_native: Some(rent).into(),
        delegated_amount: 0,
        close_authority: None.into(),
    });
    acc.lamports = rent + extra;
    acc
}

fn build_ix(
    program_id: Pubkey,
    owner: Pubkey,
    native_acc: Pubkey,
    token_id: Pubkey,
    owner_signer: bool,
) -> Instruction {
    let disc = instruction_discriminator("syncNative", 0);
    Instruction::new_with_bytes(
        program_id,
        &instruction_data(&disc, &[]),
        vec![
            AccountMeta::new(common::dummy_state_key(&program_id), false),
            AccountMeta::new(owner, owner_signer),
            AccountMeta::new(native_acc, false),
            AccountMeta::new_readonly(token_id, false),
        ],
    )
}

#[test]
fn sync_native_updates_amount() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let native_acc = Pubkey::new_unique();
    let (token_id, token_prog) = token::keyed_account();
    let ix = build_ix(program_id, owner, native_acc, token_id, true);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (
                common::dummy_state_key(&program_id),
                common::dummy_state_account(&program_id),
            ),
            (owner, funded(LAMPORTS_PER_SOL)),
            (native_acc, native_token_account(owner, EXTRA)),
            (token_id, token_prog),
        ],
        &[
            Check::success(),
            Check::return_data(&0u64.to_le_bytes()),
            Check::account(&native_acc)
                .data_slice(64, &EXTRA.to_le_bytes())
                .build(),
        ],
    );
}

#[test]
fn sync_native_does_not_require_owner_signer() {
    let (program_id, mollusk) = harness();
    let owner = Pubkey::new_unique();
    let native_acc = Pubkey::new_unique();
    let (token_id, token_prog) = token::keyed_account();
    let ix = build_ix(program_id, owner, native_acc, token_id, false);
    mollusk.process_and_validate_instruction(
        &ix,
        &[
            (
                common::dummy_state_key(&program_id),
                common::dummy_state_account(&program_id),
            ),
            (owner, funded(LAMPORTS_PER_SOL)),
            (native_acc, native_token_account(owner, EXTRA)),
            (token_id, token_prog),
        ],
        &[
            Check::success(),
            Check::account(&native_acc)
                .data_slice(64, &EXTRA.to_le_bytes())
                .build(),
        ],
    );
}
