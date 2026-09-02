mod common;

use {
    common::{harness, instruction, state_account},
    mollusk_svm::{result::Check, Mollusk},
    solana_account::Account,
    solana_instruction::AccountMeta,
    solana_program_error::ProgramError,
    solana_pubkey::Pubkey,
};

const SOURCE_STATE_LEN: usize = 2 * 8;
const LEDGER_STORAGE_LEN: usize = 4 * 8;
const MIGRATOR_STORAGE_LEN: usize = 5 * 8;
const PAYLOAD_MIGRATOR_STORAGE_LEN: usize = 6 * 8;

const UNINITIALIZED: u64 = 0;
const READY: u64 = 1;
const WRONG_DISCRIMINATOR: u64 = 2;
const UNSUPPORTED_VERSION: u64 = 3;
const MALFORMED: u64 = 4;

const INITIALIZED: u64 = 1;
const ALREADY_READY: u64 = 2;
const REJECTED: u64 = 0;

const TRANSITIONED: u64 = 1;
const ALREADY_CURRENT: u64 = 2;

const LEDGER_DISCRIMINATOR: u64 = 0x4c45_4447_4552_3101;
const CONFIG_DISCRIMINATOR: u64 = 0x434f_4e46_4947_3201;
const PAYLOAD_CONFIG_DISCRIMINATOR: u64 = 0x5041_594c_4f41_4401;

struct Fixture {
    program_id: Pubkey,
    mollusk: Mollusk,
    state_key: Pubkey,
    storage_key: Pubkey,
    source: Account,
    storage: Account,
}

fn account_after(result: &mollusk_svm::result::InstructionResult, key: &Pubkey) -> Account {
    result
        .resulting_accounts
        .iter()
        .find(|(actual, _)| actual == key)
        .expect("resulting account")
        .1
        .clone()
}

fn word(account: &Account, index: usize) -> u64 {
    let offset = index * 8;
    u64::from_le_bytes(
        account.data[offset..offset + 8]
            .try_into()
            .expect("u64 word"),
    )
}

fn set_word(account: &mut Account, index: usize, value: u64) {
    let offset = index * 8;
    account.data[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

impl Fixture {
    fn new(name: &str, env_name: &str, storage_len: usize) -> Self {
        let (program_id, mollusk) = harness(name, env_name);
        let state_key = Pubkey::new_unique();
        let storage_key = Pubkey::new_unique();
        let init = instruction(
            program_id,
            state_key,
            "initialize",
            &[0],
            true,
            true,
            vec![AccountMeta::new_readonly(storage_key, false)],
        );
        let result = mollusk.process_and_validate_instruction(
            &init,
            &[
                (state_key, state_account(&program_id, SOURCE_STATE_LEN)),
                (storage_key, state_account(&program_id, storage_len)),
            ],
            &[Check::success()],
        );
        Self {
            program_id,
            mollusk,
            state_key,
            storage_key,
            source: account_after(&result, &state_key),
            storage: account_after(&result, &storage_key),
        }
    }

    fn call(&mut self, name: &str, params: &[u64], expected: u64) {
        let ix = instruction(
            self.program_id,
            self.state_key,
            name,
            params,
            true,
            true,
            vec![AccountMeta::new(self.storage_key, false)],
        );
        let return_data = expected.to_le_bytes();
        let result = self.mollusk.process_and_validate_instruction(
            &ix,
            &[
                (self.state_key, self.source.clone()),
                (self.storage_key, self.storage.clone()),
            ],
            &[Check::success(), Check::return_data(&return_data)],
        );
        self.source = account_after(&result, &self.state_key);
        self.storage = account_after(&result, &self.storage_key);
    }
}

#[test]
fn strict_initialization_and_replay_are_distinct_and_idempotent() {
    let mut fixture = Fixture::new(
        "VersionedLedger",
        "PF_VERSIONED_LEDGER_SO",
        LEDGER_STORAGE_LEN,
    );

    fixture.call("inspectStorage", &[], UNINITIALIZED);
    fixture.call("initializeStorage", &[], INITIALIZED);
    assert_eq!(word(&fixture.storage, 1), LEDGER_DISCRIMINATOR);
    assert_eq!(word(&fixture.storage, 2), 1);
    fixture.call("inspectStorage", &[], READY);

    let before_replay = fixture.storage.data.clone();
    fixture.call("initializeStorage", &[], ALREADY_READY);
    assert_eq!(fixture.storage.data, before_replay, "replay must not write");

    fixture.call("record", &[77], 77);
    fixture.call("current", &[], 77);
    assert_eq!(word(&fixture.storage, 3), 77);
}

#[test]
fn strict_policy_distinguishes_foreign_unsupported_and_malformed_headers() {
    let cases = [
        (7, 1, WRONG_DISCRIMINATOR),
        (LEDGER_DISCRIMINATOR, 9, UNSUPPORTED_VERSION),
        (0, 1, MALFORMED),
        (LEDGER_DISCRIMINATOR, 0, MALFORMED),
    ];

    for (discriminator, version, expected_status) in cases {
        let mut fixture = Fixture::new(
            "VersionedLedger",
            "PF_VERSIONED_LEDGER_SO",
            LEDGER_STORAGE_LEN,
        );
        set_word(&mut fixture.storage, 1, discriminator);
        set_word(&mut fixture.storage, 2, version);

        fixture.call("inspectStorage", &[], expected_status);
        let before = fixture.storage.data.clone();
        fixture.call("initializeStorage", &[], REJECTED);
        assert_eq!(
            fixture.storage.data, before,
            "incompatible initialization must be atomic"
        );

        let ix = instruction(
            fixture.program_id,
            fixture.state_key,
            "record",
            &[91],
            true,
            true,
            vec![AccountMeta::new(fixture.storage_key, false)],
        );
        let source_before = fixture.source.data.clone();
        fixture.mollusk.process_and_validate_instruction(
            &ix,
            &[
                (fixture.state_key, fixture.source),
                (fixture.storage_key, fixture.storage),
            ],
            &[
                Check::err(ProgramError::Custom(1)),
                Check::account(&fixture.state_key)
                    .data(&source_before)
                    .build(),
                Check::account(&fixture.storage_key).data(&before).build(),
            ],
        );
    }
}

#[test]
fn short_account_fails_closed_during_inspection_and_initialization() {
    for name in ["inspectStorage", "initializeStorage"] {
        let fixture = Fixture::new("VersionedLedger", "PF_VERSIONED_LEDGER_SO", 2 * 8);
        let before = fixture.storage.data.clone();
        let ix = instruction(
            fixture.program_id,
            fixture.state_key,
            name,
            &[],
            true,
            true,
            vec![AccountMeta::new(fixture.storage_key, false)],
        );
        fixture.mollusk.process_and_validate_instruction(
            &ix,
            &[
                (fixture.state_key, fixture.source),
                (fixture.storage_key, fixture.storage),
            ],
            &[
                Check::err(ProgramError::Custom(1)),
                Check::account(&fixture.storage_key).data(&before).build(),
            ],
        );
    }
}

#[test]
fn migration_policy_requires_the_single_explicit_version_edge() {
    let mut fixture = Fixture::new(
        "VersionedMigrator",
        "PF_VERSIONED_MIGRATOR_SO",
        MIGRATOR_STORAGE_LEN,
    );
    set_word(&mut fixture.storage, 1, CONFIG_DISCRIMINATOR);
    set_word(&mut fixture.storage, 2, 1);

    fixture.call("inspectStorage", &[], UNSUPPORTED_VERSION);
    let before_initialize = fixture.storage.data.clone();
    fixture.call("initializeStorage", &[], REJECTED);
    assert_eq!(
        fixture.storage.data, before_initialize,
        "initialization must not migrate"
    );

    fixture.call("migrateV1", &[], TRANSITIONED);
    assert_eq!(word(&fixture.storage, 2), 2);
    fixture.call("inspectStorage", &[], READY);

    let before_replay = fixture.storage.data.clone();
    fixture.call("migrateV1", &[], ALREADY_CURRENT);
    assert_eq!(
        fixture.storage.data, before_replay,
        "transition replay must not write"
    );
    fixture.call("setCurrent", &[88], 88);
    fixture.call("current", &[], 88);

    set_word(&mut fixture.storage, 2, 3);
    let before_unlisted = fixture.storage.data.clone();
    fixture.call("migrateV1", &[], REJECTED);
    assert_eq!(
        fixture.storage.data, before_unlisted,
        "unlisted source version must not move"
    );
}

#[test]
fn payload_migration_copies_legacy_word_then_publishes_version() {
    let mut fixture = Fixture::new(
        "VersionedPayloadMigrator",
        "PF_VERSIONED_PAYLOAD_MIGRATOR_SO",
        PAYLOAD_MIGRATOR_STORAGE_LEN,
    );
    set_word(&mut fixture.storage, 1, PAYLOAD_CONFIG_DISCRIMINATOR);
    set_word(&mut fixture.storage, 2, 1);
    set_word(&mut fixture.storage, 4, 77);
    set_word(&mut fixture.storage, 5, 0);

    fixture.call("inspectStorage", &[], UNSUPPORTED_VERSION);
    let before_initialize = fixture.storage.data.clone();
    fixture.call("initializeStorage", &[], REJECTED);
    assert_eq!(
        fixture.storage.data, before_initialize,
        "initialization must not migrate payload"
    );

    fixture.call("migrateV1", &[], TRANSITIONED);
    assert_eq!(word(&fixture.storage, 2), 2);
    assert_eq!(word(&fixture.storage, 5), 77, "legacy word 4 must copy into word 5");
    fixture.call("inspectStorage", &[], READY);
    fixture.call("current", &[], 77);

    let before_replay = fixture.storage.data.clone();
    fixture.call("migrateV1", &[], ALREADY_CURRENT);
    assert_eq!(
        fixture.storage.data, before_replay,
        "payload transition replay must not write"
    );

    fixture.call("setCurrent", &[88], 88);
    fixture.call("current", &[], 88);
}
