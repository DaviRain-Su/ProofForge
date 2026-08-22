namespace ProofForge.Crypto.Sha256

/-- FIPS 180-4 SHA-256。本机纯函数，能进 `#guard`。不是链上 syscall。 -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

private def hexByte (b : UInt8) : String :=
  let n := b.toNat
  String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))

private def shr (x : UInt32) (n : Nat) : UInt32 :=
  UInt32.ofNat (x.toNat >>> n)

private def shl (x : UInt32) (n : Nat) : UInt32 :=
  UInt32.ofNat ((x.toNat <<< (n % 32)) % 4294967296)

private def rotr (x : UInt32) (n : Nat) : UInt32 :=
  let n := n % 32
  shr x n ||| shl x ((32 - n) % 32)

private def ch (e f g : UInt32) : UInt32 :=
  (e &&& f) ^^^ ((~~~e) &&& g)

private def maj (a b c : UInt32) : UInt32 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

private def bigSigma0 (a : UInt32) : UInt32 :=
  rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22

private def bigSigma1 (e : UInt32) : UInt32 :=
  rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25

private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def wordBE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  shl b0.toUInt32 24 ||| shl b1.toUInt32 16 ||| shl b2.toUInt32 8 ||| b3.toUInt32

private def pad (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let bitLen := msg.size * 8
    let mut out := msg.push 0x80
    while out.size % 64 != 56 do
      out := out.push 0
    let mut len := bitLen
    let mut be : Array UInt8 := #[]
    for _ in [0:8] do
      be := #[UInt8.ofNat (len % 256)] ++ be
      len := len / 256
    return out ++ be

private def schedule (block : Array UInt8) : Array UInt32 :=
  Id.run do
    let mut w : Array UInt32 := #[]
    for i in [0:16] do
      let o := i * 4
      w := w.push (wordBE block[o]! block[o + 1]! block[o + 2]! block[o + 3]!)
    for i in [16:64] do
      w := w.push (w[i - 16]! + smallSigma0 w[i - 15]! + w[i - 7]! + smallSigma1 w[i - 2]!)
    return w

private def compress (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  let w := schedule block
  Id.run do
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [0:64] do
      let t1 := hh + bigSigma1 e + ch e f g + K[i]! + w[i]!
      let t2 := bigSigma0 a + maj a b c
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return #[
      h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
      h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh
    ]

private def wordsToBytes (h : Array UInt32) : Array UInt8 :=
  Id.run do
    let mut out : Array UInt8 := #[]
    for w in h do
      let n := w.toNat
      out := out.push (UInt8.ofNat ((n >>> 24) % 256))
      out := out.push (UInt8.ofNat ((n >>> 16) % 256))
      out := out.push (UInt8.ofNat ((n >>> 8) % 256))
      out := out.push (UInt8.ofNat (n % 256))
    return out

/-- 32 字节 digest。 -/
def digestBytes (s : String) : Array UInt8 :=
  let padded := pad s.toUTF8.data
  let nBlocks := padded.size / 64
  Id.run do
    let mut h := H0
    for i in [0:nBlocks] do
      let off := i * 64
      let mut block : Array UInt8 := #[]
      for j in [0:64] do
        block := block.push padded[off + j]!
      h := compress h block
    return wordsToBytes h

/-- 64 个小写十六进制字符。 -/
def digestHex (s : String) : String :=
  String.intercalate "" ((digestBytes s).toList.map hexByte)

/-- 前 8 字节按小端读成 u64。disc 用这个。 -/
def first8Le (s : String) : UInt64 :=
  let d := digestBytes s
  Id.run do
    let mut v : UInt64 := 0
    for i in [0:8] do
      v := v ||| (d[i]!.toUInt64 <<< UInt64.ofNat (8 * i))
    return v

/-- 前 8 字节按大端读成 u64。layout marker 用这个。 -/
def first8Be (s : String) : UInt64 :=
  let d := digestBytes s
  Id.run do
    let mut v : UInt64 := 0
    for i in [0:8] do
      v := (v <<< 8) ||| d[i]!.toUInt64
    return v

end ProofForge.Crypto.Sha256
