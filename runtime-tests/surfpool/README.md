# Surfpool deployment smoke

`smoke.sh` builds Phoenix, starts an offline headless Surfpool v1.5.0 Surfnet, and runs the
`deployment` IaC runbook. The runbook deliberately sets `instant_surfnet_deployment = false`, so
`svm::deploy_program` creates and writes the buffer and finalizes the program through normal
Upgradeable Loader-v3 transactions instead of the `surfnet_writeProgram` direct-state cheatcode.

```bash
runtime-tests/surfpool/smoke.sh
```

The script generates temporary payer/program keypairs under ignored `build/surfpool`, receives a
local-only Surfnet airdrop, and checks the confirmed deploy signature, executable Loader-v3 program
account, ProgramData size, and the complete on-chain ELF bytes against the local artifact. It never
contacts devnet/mainnet and does not use `solana-test-validator`. Private key files and the runbook
recovery log are removed when the script exits; non-secret RPC evidence remains under `build`.

Successful local deployment proves that the current Phoenix ELF passed Surfpool's transaction and
Loader path. It is not a public-network deployment claim.
