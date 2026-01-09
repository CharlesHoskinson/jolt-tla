/-!
# SHA-256 Implementation

Pure Lean implementation of SHA-256 (FIPS 180-4) for registry hash computation.

## Main Definitions
* `sha256` - Compute SHA-256 hash of ByteArray
* `sha256Hex` - Compute SHA-256 and return as hex string

## References
* FIPS 180-4: Secure Hash Standard
* Jolt Spec §3.3: JOLT_PARAMETER_REGISTRY_HASH_V1 = SHA-256(canonical_registry_bytes)
-/

namespace Jolt.Hash

/-- SHA-256 initial hash values (first 32 bits of fractional parts of square roots of first 8 primes). -/
private def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-- SHA-256 round constants (first 32 bits of fractional parts of cube roots of first 64 primes). -/
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

/-- Right rotate a 32-bit word. -/
private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 Ch function. -/
private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- SHA-256 Maj function. -/
private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- SHA-256 Σ0 function. -/
private def sigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- SHA-256 Σ1 function. -/
private def sigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- SHA-256 σ0 function. -/
private def lsigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- SHA-256 σ1 function. -/
private def lsigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Read a 32-bit big-endian word from bytes. -/
private def readBE32 (data : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := data.get! offset |>.toUInt32
  let b1 := data.get! (offset + 1) |>.toUInt32
  let b2 := data.get! (offset + 2) |>.toUInt32
  let b3 := data.get! (offset + 3) |>.toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Write a 32-bit big-endian word to bytes. -/
private def writeBE32 (w : UInt32) : ByteArray :=
  let b0 := (w >>> 24).toUInt8
  let b1 := (w >>> 16).toUInt8
  let b2 := (w >>> 8).toUInt8
  let b3 := w.toUInt8
  ByteArray.mk #[b0, b1, b2, b3]

/-- Pad message according to SHA-256 specification. -/
private def padMessage (data : ByteArray) : ByteArray := Id.run do
  let msgLen := data.size
  let bitLen := msgLen * 8

  -- Append 0x80 byte
  let mut padded := data.push 0x80

  -- Pad with zeros until length ≡ 448 mod 512 bits (56 mod 64 bytes)
  let targetLen := ((msgLen + 9 + 63) / 64) * 64
  let zerosNeeded := targetLen - msgLen - 9
  for _ in [:zerosNeeded] do
    padded := padded.push 0x00

  -- Append original length as 64-bit big-endian
  -- Note: For messages < 2^32 bytes, high 32 bits are zero
  for _ in [:4] do
    padded := padded.push 0x00
  padded := padded.push ((bitLen >>> 24) &&& 0xFF).toUInt8
  padded := padded.push ((bitLen >>> 16) &&& 0xFF).toUInt8
  padded := padded.push ((bitLen >>> 8) &&& 0xFF).toUInt8
  padded := padded.push (bitLen &&& 0xFF).toUInt8

  padded

/-- Process a single 512-bit (64-byte) block. -/
private def processBlock (hash : Array UInt32) (block : ByteArray) (blockOffset : Nat) : Array UInt32 := Id.run do
  -- Create message schedule W[0..63]
  let mut w : Array UInt32 := #[]

  -- W[0..15] from block
  for i in [:16] do
    w := w.push (readBE32 block (blockOffset + i * 4))

  -- W[16..63] from schedule
  for i in [16:64] do
    let s0 := lsigma0 w[i - 15]!
    let s1 := lsigma1 w[i - 2]!
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)

  -- Initialize working variables
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!

  -- 64 rounds
  for i in [:64] do
    let t1 := h + sigma1 e + ch e f g + K[i]! + w[i]!
    let t2 := sigma0 a + maj a b c
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2

  -- Add to hash
  #[hash[0]! + a, hash[1]! + b, hash[2]! + c, hash[3]! + d,
    hash[4]! + e, hash[5]! + f, hash[6]! + g, hash[7]! + h]

/-- Compute SHA-256 hash of input bytes. Returns 32-byte hash. -/
def sha256 (data : ByteArray) : ByteArray := Id.run do
  let padded := padMessage data
  let numBlocks := padded.size / 64

  let mut hash := H0

  for i in [:numBlocks] do
    hash := processBlock hash padded (i * 64)

  -- Convert hash words to bytes
  let mut result := ByteArray.empty
  for h in hash do
    result := result ++ writeBE32 h

  result

/-- Convert nibble (0-15) to hex character. -/
private def nibbleToHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

/-- Convert byte to 2-character lowercase hex string. -/
private def byteToHexLower (b : UInt8) : String :=
  let hi := (b.toNat >>> 4) &&& 0xF
  let lo := b.toNat &&& 0xF
  String.ofList [nibbleToHex hi, nibbleToHex lo]

/-- Compute SHA-256 hash and return as lowercase hex string. -/
def sha256Hex (data : ByteArray) : String := Id.run do
  let hash := sha256 data
  let mut result := ""
  for b in hash.data do
    result := result ++ byteToHexLower b
  result

end Jolt.Hash
