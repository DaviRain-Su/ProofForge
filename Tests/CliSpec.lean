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

#guard ProofForge.Cli.svmModuleName "Phoenix" == `Examples.Svm.Phoenix
#guard ProofForge.Cli.svmModuleName "Counter" == `Examples.Counter
#guard ProofForge.Cli.fixtureModule .evm "Counter" == `Examples.Counter
#guard ProofForge.Cli.fixtureModule .evm "TipJar" == `Examples.Evm.TipJar
#guard ProofForge.Cli.fixtureModule .evm "EvmTokenErgonomics" == `Examples.EvmTokenErgonomics
#guard ProofForge.Cli.fixtureModule .near "NearPromiseHandle" == `Examples.NearPromiseHandle
#guard ProofForge.Cli.fixtureModule .xrpl "XrplSmoke" == `Examples.Xrpl.XrplSmoke
#guard ProofForge.Cli.fixtureModule .near "NearCtx" == `Examples.Near.NearCtx

#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "xrpl-alphanet", "XrplSmoke"] with
  | .ok o => o.command == .build && o.target == .xrplAlphaNet && o.names == #["XrplSmoke"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["deploy", "XrplSmoke"] with
  | .ok o => o.command == .deploy && o.target == .xrplAlphaNet && o.names == #["XrplSmoke"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs
      ["deploy", "--target", "xrpl", "--rpc", "http://127.0.0.1:15005",
        "--send-amount", "2000000000", "XrplSmoke"] with
  | .ok o =>
      o.command == .deploy && o.target == .xrpl && o.sendAmount == "2000000000" &&
        o.rpcUrl == "http://127.0.0.1:15005" && o.names == #["XrplSmoke"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs
      ["call", "--target", "xrpl-alphanet", "--contract", "rC", "increment", "1"] with
  | .ok o =>
      o.command == .call && o.functionName == "increment" && o.callArgs == #["1"]
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs
      ["call", "--contract", "rContract", "bump"] with
  | .ok o =>
      o.command == .call && o.target == .xrplAlphaNet &&
        o.contract == "rContract" && o.functionName == "bump" && o.callArgs.isEmpty
  | .error _ => false

end Tests.CliSpec
