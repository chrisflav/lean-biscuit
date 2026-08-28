import LeanBiscuit.Util.Bytes

/-!
# SHA-256

ECDSA over secp256r1, the second signature algorithm biscuit supports, hashes
its messages with SHA-256.  As with `Sha512`, this is a direct transcription of
FIPS 180-4.
-/

namespace LeanBiscuit
namespace Sha256

/-- The sixty-four round constants. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Read the big-endian 32 bit word at byte offset `off`. -/
def word (b : Bytes) (off : Nat) : UInt32 :=
  let rec go (i : Nat) (acc : UInt32) : UInt32 :=
    match i with
    | 0 => acc
    | i + 1 => go i (acc <<< 8 ||| (b[off + (4 - (i + 1))]!).toUInt32)
  go 4 0

/-- The message schedule for one 64 byte block. -/
def schedule (b : Bytes) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (word b (off + i * 4))
  for i in [16:64] do
    w := w.push (w[i - 16]! + smallSigma0 w[i - 15]! + w[i - 7]! + smallSigma1 w[i - 2]!)
  return w

/-- Compress one 64 byte block into the running state. -/
def compress (h : Array UInt32) (b : Bytes) (off : Nat) : Array UInt32 := Id.run do
  let w := schedule b off
  let mut a := h[0]!; let mut bb := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:64] do
    let t1 := hh + bigSigma1 e + ch e f g + K[i]! + w[i]!
    let t2 := bigSigma0 a + maj a bb c
    hh := g; g := f; f := e; e := d + t1
    d := c; c := bb; bb := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + bb, h[2]! + c, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Append the FIPS 180-4 padding for a 512 bit block size. -/
def pad (msg : Bytes) : Bytes :=
  let len := msg.size
  let rem := (len + 1) % 64
  let zeros := if rem ≤ 56 then 56 - rem else 120 - rem
  msg.push 0x80 ++ Bytes.ofList (List.replicate zeros 0) ++ Bytes.ofNatBE 8 (len * 8)

/-- The SHA-256 digest of a byte string (32 bytes). -/
def hash (msg : Bytes) : Bytes := Id.run do
  let m := pad msg
  let mut h := H0
  for i in [0:m.size / 64] do
    h := compress h m (i * 64)
  let mut out := ByteArray.empty
  for x in h do
    out := out ++ Bytes.ofNatBE 4 x.toNat
  return out

end Sha256
end LeanBiscuit
