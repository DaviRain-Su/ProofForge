import ProofForge.Cli

namespace Tests.CliSpec

#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "svm", "--out", "build/sbpf", "Counter"] with
  | .ok o => o.outDir.toString == "build/sbpf" && o.names == #["Counter"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["build", "Counter", "--out", "build/tmp"] with
  | .ok o => o.outDir.toString == "build/tmp" && o.names == #["Counter"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["build", "Counter", "Pair", "--out", "out", "--target", "evm"] with
  | .ok o => o.target == .evm && o.outDir.toString == "out" && o.names == #["Counter", "Pair"]
  | .error _ => false

#guard ProofForge.Cli.svmModuleName "Phoenix" == `Projects.Phoenix
#guard ProofForge.Cli.svmModuleName "Counter" == `Examples.Counter
#guard ProofForge.Cli.projectPrograms.contains "Phoenix"

end Tests.CliSpec
