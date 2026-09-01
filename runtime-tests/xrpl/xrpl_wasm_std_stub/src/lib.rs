//! Compilation stub of the xrpl_wasm_std surface consumed by ProofForge-generated
//! XRPL Bedrock sources. Deployable=false; runtime gate only.

pub mod core {
    pub mod current_tx {
        pub mod contract_call {
            pub struct ContractCall;
            pub fn get_current_contract_call() -> ContractCall {
                ContractCall
            }
        }
        pub mod traits {
            pub trait ContractCallFields {
                fn get_contract_account(&self) -> Option<[u8; 20]>;
            }
            impl ContractCallFields for super::contract_call::ContractCall {
                fn get_contract_account(&self) -> Option<[u8; 20]> {
                    Some([0u8; 20])
                }
            }
        }
    }
    pub mod data {
        pub mod codec {
            pub fn get_data<T>(_account: &[u8; 20], _key: &str) -> Option<T> {
                None
            }
            pub fn set_data<T>(_account: &[u8; 20], _key: &str, _value: T) -> Result<(), i32> {
                Ok(())
            }
        }
    }
}
