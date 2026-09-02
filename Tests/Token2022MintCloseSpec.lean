import Examples.Svm.Token2022MintClose
import ProofForge

namespace Tests.Token2022MintCloseSpec

open ProofForge.Svm.Sdk
open ProofForge.Svm.Cpi.TokenTlv

#guard Token2022.mintCloseAuthorityType == 3
#guard Token2022.mintCloseAuthorityBodyLen == 32
#guard Token2022.mintClosePolicy == (.token2022MintClose : Policy)

/-- Classic 82-byte mint: closed and mint-close policies both accept (no TLV region). -/
private def classicMint : Array UInt8 := Array.replicate mintBaseLen 0

#guard evaluatePolicy (.token2022Base .mint) (Token2022.viewOf classicMint) == .accept
#guard evaluatePolicy .token2022MintClose (Token2022.viewOf classicMint) == .accept
#guard Token2022.parseMintCloseAuthority classicMint == none

/-- Build a mint buffer: 82 base + 83 zero pad + type byte 1 + TLV entries. -/
private def mintWithTlv (entries : Array (UInt64 × Array UInt8)) : Array UInt8 := Id.run do
  let mut data := Array.replicate mintBaseLen (0 : UInt8)
  data := data ++ Array.replicate mintPaddingBytes 0
  data := data.push 1 -- AccountType::Mint
  for (ty, body) in entries do
    data := data.push (UInt8.ofNat (ty.toNat % 256))
    data := data.push (UInt8.ofNat (ty.toNat / 256))
    data := data.push (UInt8.ofNat (body.size % 256))
    data := data.push (UInt8.ofNat (body.size / 256))
    data := data ++ body
  pure data

private def closeBody : Array UInt8 := Array.replicate 32 7

private def mintCloseOnly : Array UInt8 :=
  mintWithTlv #[(mintCloseAuthorityType, closeBody)]

#guard evaluatePolicy .token2022MintClose (Token2022.viewOf mintCloseOnly) == .accept
#guard evaluatePolicy (.token2022Base .mint) (Token2022.viewOf mintCloseOnly) != .accept

#guard
  match Token2022.parseMintCloseAuthority mintCloseOnly with
  | some v => v.wellFormed && v.bytes == closeBody
  | none => false

/-- Transfer-fee mint (type 1) stays reject under mint-close policy. -/
private def feeMint : Array UInt8 :=
  mintWithTlv #[(1, Array.replicate 108 0)]

#guard evaluatePolicy .token2022MintClose (Token2022.viewOf feeMint) != .accept
#guard Token2022.parseMintCloseAuthority feeMint == none

#guard (Examples.Svm.Token2022MintClose.init 0).dummy == 0
#guard Examples.Svm.Token2022MintClose.get (Examples.Svm.Token2022MintClose.init 0) == 0

end Tests.Token2022MintCloseSpec
