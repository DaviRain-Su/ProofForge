import ProofForge

namespace Tests.IdlSpec

#guard
  let idl := ProofForge.Idl.emitIdl ProofForge.Golden.extractedCounter
  idl.contains "\"spec\": \"0.1.0\"" &&
    idl.contains "\"name\": \"Counter\"" &&
    idl.contains "\"name\": \"increment\"" &&
    idl.contains "\"name\": \"initialize\"" &&
    idl.contains "\"discriminator\"" &&
    idl.contains "\"type\":\"u64\"" &&
    !idl.contains "solana_entry"

#guard
  (ProofForge.Idl.discBytes "increment" 1).size == 8

#guard
  (ProofForge.Idl.layoutDiscBytes ProofForge.Golden.extractedCounter).size == 8

end Tests.IdlSpec
