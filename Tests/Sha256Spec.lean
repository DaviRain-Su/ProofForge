import ProofForge

#guard ProofForge.Sha256.digestHex "" ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

#guard ProofForge.Sha256.digestHex "abc" ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

#guard
  match ProofForge.IR.discHexOf "initialize" 1 with
  | .ok "0x642858a76747495e" => true
  | _ => false
