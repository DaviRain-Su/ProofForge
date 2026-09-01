namespace ProofForge.Svm.Memo.Ascii

/-- ProofForge's static Memo payload budget. It stays below the shared 1,024-byte CPI scratch
budget after instruction/account descriptors are included. -/
def maxBytes : Nat := 512

/-- Bounded seven-bit payload policy. Seven-bit input makes `String.length` the encoded byte
length; runtime UTF-8 encoding and dynamic byte buffers remain outside this contract. -/
def wellFormed (value : String) : Bool :=
  value.length ≤ maxBytes && value.toList.all (·.toNat < 128)

end ProofForge.Svm.Memo.Ascii

namespace ProofForge.Svm.Memo.Utf8

/-- Same CPI scratch budget as ASCII Memo; counted in UTF-8 **bytes**, not Unicode scalars. -/
def maxBytes : Nat := Ascii.maxBytes

private def isContinuation (byte : Nat) : Bool := 0x80 ≤ byte && byte ≤ 0xbf

/-- Strict Unicode-scalar UTF-8 validation over a raw byte buffer. Rejects truncated, overlong,
surrogate, and greater-than-U+10FFFF encodings, and enforces the Memo byte ceiling. -/
def bytesWellFormed (bytes : ByteArray) : Bool := Id.run do
  if bytes.size > maxBytes then
    return false
  let length := bytes.size
  let mut index := 0
  let mut valid := true
  -- Bound the scan by `maxBytes + 1` so the loop is statically finite.
  for _ in [0:maxBytes + 1] do
    if valid && index < length then
      let b0 := (bytes.get! index).toNat
      if b0 ≤ 0x7f then
        index := index + 1
      else if 0xc2 ≤ b0 && b0 ≤ 0xdf then
        if index + 2 ≤ length then
          let b1 := (bytes.get! (index + 1)).toNat
          if isContinuation b1 then index := index + 2 else valid := false
        else valid := false
      else if 0xe0 ≤ b0 && b0 ≤ 0xef then
        if index + 3 ≤ length then
          let b1 := (bytes.get! (index + 1)).toNat
          let b2 := (bytes.get! (index + 2)).toNat
          let firstContinuation :=
            if b0 == 0xe0 then 0xa0 ≤ b1 && b1 ≤ 0xbf
            else if b0 == 0xed then 0x80 ≤ b1 && b1 ≤ 0x9f
            else isContinuation b1
          if firstContinuation && isContinuation b2 then index := index + 3
          else valid := false
        else valid := false
      else if 0xf0 ≤ b0 && b0 ≤ 0xf4 then
        if index + 4 ≤ length then
          let b1 := (bytes.get! (index + 1)).toNat
          let b2 := (bytes.get! (index + 2)).toNat
          let b3 := (bytes.get! (index + 3)).toNat
          let firstContinuation :=
            if b0 == 0xf0 then 0x90 ≤ b1 && b1 ≤ 0xbf
            else if b0 == 0xf4 then 0x80 ≤ b1 && b1 ≤ 0x8f
            else isContinuation b1
          if firstContinuation && isContinuation b2 && isContinuation b3 then
            index := index + 4
          else valid := false
        else valid := false
      else
        valid := false
  return valid && index == length

/-- Bounded UTF-8 Memo payload. Lean `String` values always encode to well-formed UTF-8; the gate
still runs the byte scanner so raw-buffer callers share one fail-closed contract. -/
def wellFormed (value : String) : Bool :=
  bytesWellFormed value.toUTF8

end ProofForge.Svm.Memo.Utf8
