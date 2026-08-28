import LeanBiscuit.Util.Bytes
import LeanBiscuit.Crypto.Sha256
import LeanBiscuit.Crypto.Hmac

/-!
# ECDSA over secp256r1 (NIST P-256)

The second signature algorithm supported by biscuit.  Public keys use the
compressed SEC1 encoding (33 bytes, prefix `02` or `03`) and signatures use the
SEC1 ASN.1 DER `SEQUENCE { r INTEGER, s INTEGER }` encoding.

Points are represented in Jacobian coordinates `(X : Y : Z)` with
`x = X/Z²`, `y = Y/Z³`; the point at infinity is `Z = 0`.
-/

namespace LeanBiscuit
namespace P256

/-- The field characteristic `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def p : Nat := 115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- The order of the base point. -/
def n : Nat := 115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- The curve coefficient `b`; the coefficient `a` is `-3`. -/
def b : Nat := 41058363725152142129326129780047268409114441015993725554835256314039467401291

/-- The `x` coordinate of the base point. -/
def Gx : Nat := 48439561293906451759052585252797914202762949526041747995844080717082404635286

/-- The `y` coordinate of the base point. -/
def Gy : Nat := 36134250956749795798585127919587881956611106672985015071877198253568414405109

namespace F

@[inline] def add (a b : Nat) : Nat := (a + b) % p
@[inline] def sub (a b : Nat) : Nat := (a + p - b % p) % p
@[inline] def mul (a b : Nat) : Nat := (a * b) % p
@[inline] def neg (a : Nat) : Nat := (p - a % p) % p

/-- Square-and-multiply accumulator for `pow`. -/
def powAux (b e acc : Nat) : Nat :=
  if _h : e = 0 then acc
  else powAux (b * b % p) (e / 2) (if e % 2 == 1 then acc * b % p else acc)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Modular exponentiation. -/
def pow (base e : Nat) : Nat := powAux (base % p) e 1

/-- Multiplicative inverse, via Fermat's little theorem. -/
def inv (a : Nat) : Nat := pow a (p - 2)

end F

namespace N

/-- Square-and-multiply accumulator for exponentiation modulo the group order. -/
def powAux (b e acc : Nat) : Nat :=
  if _h : e = 0 then acc
  else powAux (b * b % n) (e / 2) (if e % 2 == 1 then acc * b % n else acc)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Multiplicative inverse modulo the group order. -/
def inv (a : Nat) : Nat := powAux (a % n) (n - 2) 1

end N

/-- A curve point in Jacobian coordinates; `Z = 0` denotes the point at infinity. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  deriving Repr

namespace Point

/-- The point at infinity. -/
def infinity : Point := ⟨1, 1, 0⟩

/-- Is this the point at infinity? -/
def isInfinity (P : Point) : Bool := P.Z == 0

/-- The base point. -/
def base : Point := ⟨Gx, Gy, 1⟩

/-- Point doubling, using the `a = -3` shortcut. -/
def double (P : Point) : Point :=
  if P.Z == 0 || P.Y == 0 then infinity
  else
    let yy := F.mul P.Y P.Y
    let a := F.mul 4 (F.mul P.X yy)
    let bq := F.mul 8 (F.mul yy yy)
    let zz := F.mul P.Z P.Z
    let c := F.mul 3 (F.mul (F.sub P.X zz) (F.add P.X zz))
    let dd := F.sub (F.mul c c) (F.mul 2 a)
    ⟨dd, F.sub (F.mul c (F.sub a dd)) bq, F.mul 2 (F.mul P.Y P.Z)⟩

/-- Point addition. -/
def add (P Q : Point) : Point :=
  if P.Z == 0 then Q
  else if Q.Z == 0 then P
  else
    let z1z1 := F.mul P.Z P.Z
    let z2z2 := F.mul Q.Z Q.Z
    let u1 := F.mul P.X z2z2
    let u2 := F.mul Q.X z1z1
    let s1 := F.mul P.Y (F.mul z2z2 Q.Z)
    let s2 := F.mul Q.Y (F.mul z1z1 P.Z)
    if u1 == u2 then
      if s1 == s2 then double P else infinity
    else
      let h := F.sub u2 u1
      let r := F.sub s2 s1
      let hh := F.mul h h
      let hhh := F.mul h hh
      let u1hh := F.mul u1 hh
      let x3 := F.sub (F.sub (F.mul r r) hhh) (F.mul 2 u1hh)
      ⟨x3, F.sub (F.mul r (F.sub u1hh x3)) (F.mul s1 hhh),
        F.mul h (F.mul P.Z Q.Z)⟩

/-- The binary digits of `k`, most significant first. -/
def bits (k : Nat) (acc : List Bool) : List Bool :=
  if _h : k = 0 then acc else bits (k / 2) ((k % 2 == 1) :: acc)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Scalar multiplication by double-and-add. -/
def smul (k : Nat) (P : Point) : Point :=
  (bits k []).foldl (fun acc bit => let acc := double acc; if bit then add acc P else acc) infinity

/-- The affine `x` coordinate, or `none` at infinity. -/
def affineX (P : Point) : Option Nat :=
  if P.Z == 0 then none
  else
    let zi := F.inv P.Z
    some (F.mul P.X (F.mul zi zi))

end Point

/-- Decode a compressed SEC1 public key (33 bytes, prefix `02` or `03`). -/
def decodePublicKey (key : Bytes) : Option Point := do
  if key.size != 33 then none else
  let tag := key[0]!
  if tag != 2 && tag != 3 then none else
  let x := Bytes.toNatBE (key.extract 1 33)
  if x ≥ p then none else
  -- y² = x³ - 3x + b
  let rhs := F.add (F.sub (F.mul x (F.mul x x)) (F.mul 3 x)) b
  let y := F.pow rhs ((p + 1) / 4)
  if F.mul y y != rhs then none else
  let wantOdd := tag == 3
  let y := if (y % 2 == 1) == wantOdd then y else F.neg y
  some ⟨x, y, 1⟩

/-! A minimal ASN.1 DER reader for `SEQUENCE { r INTEGER, s INTEGER }`. -/
namespace Der

/-- Read a DER length at `i`; returns the length and the offset of the contents. -/
def readLength (data : Bytes) (i : Nat) : Option (Nat × Nat) := do
  if i ≥ data.size then none else
  let b0 := (data[i]!).toNat
  if b0 < 0x80 then some (b0, i + 1)
  else
    let count := b0 - 0x80
    -- long form: DER forbids the indefinite form and requires a minimal encoding
    if count == 0 || count > 4 || i + 1 + count > data.size then none else
    let len := Bytes.toNatBE (data.extract (i + 1) (i + 1 + count))
    if len < 0x80 then none else
    some (len, i + 1 + count)

/-- Read a DER `INTEGER` at `i`; returns its value and the next offset.
Rejects negative and non-minimally encoded values, as DER requires. -/
def readInteger (data : Bytes) (i : Nat) : Option (Nat × Nat) := do
  if i ≥ data.size then none else
  if data[i]! != 0x02 then none else
  let (len, contents) ← readLength data (i + 1)
  if len == 0 || contents + len > data.size then none else
  let body := data.extract contents (contents + len)
  if body[0]! &&& 0x80 != 0 then none else
  if len > 1 && body[0]! == 0 && body[1]! &&& 0x80 == 0 then none else
  some (Bytes.toNatBE body, contents + len)

/-- The minimal big-endian byte list of a natural number; empty for zero. -/
def minimalBE (n : Nat) (acc : List UInt8) : List UInt8 :=
  if _h : n = 0 then acc else minimalBE (n / 256) (UInt8.ofNat (n % 256) :: acc)
termination_by n
decreasing_by omega

/-- Encode a non-negative integer as a DER `INTEGER` body: big-endian, minimal,
with a leading zero when the top bit would otherwise make it negative. -/
def integerBody (n : Nat) : Bytes :=
  let body := minimalBE n []
  let body := if body.isEmpty then [0] else body
  let body := if body.head! &&& 0x80 != 0 then 0 :: body else body
  Bytes.ofList body

/-- Encode a DER length. -/
def encodeLength (n : Nat) : Bytes :=
  if n < 0x80 then Bytes.ofList [UInt8.ofNat n]
  else
    let body := minimalBE n []
    Bytes.ofList (UInt8.ofNat (0x80 + body.length) :: body)

/-- Encode an ECDSA signature in SEC1 ASN.1 DER form. -/
def encodeSignature (r s : Nat) : Bytes :=
  let rb := integerBody r
  let sb := integerBody s
  let contents :=
    Bytes.ofList [0x02] ++ encodeLength rb.size ++ rb
      ++ Bytes.ofList [0x02] ++ encodeLength sb.size ++ sb
  Bytes.ofList [0x30] ++ encodeLength contents.size ++ contents

/-- Parse an ECDSA signature in SEC1 ASN.1 DER form. -/
def parseSignature (data : Bytes) : Option (Nat × Nat) := do
  if data.size == 0 || data[0]! != 0x30 then none else
  let (len, contents) ← readLength data 1
  if contents + len != data.size then none else
  let (r, i) ← readInteger data contents
  let (s, i) ← readInteger data i
  if i != data.size then none else
  some (r, s)

end Der

/-- Why an ECDSA verification failed. -/
inductive Failure where
  /-- The signature was not valid DER. -/
  | badSignatureEncoding
  /-- The public key could not be decoded. -/
  | badPoint
  /-- `r` or `s` was out of range. -/
  | outOfRange
  /-- The verification equation did not hold. -/
  | equation
  deriving Repr, DecidableEq

/-- The compressed SEC1 encoding of a point. -/
def encodePoint (P : Point) : Option Bytes := do
  if P.Z == 0 then none else
  let zi := F.inv P.Z
  let zi2 := F.mul zi zi
  let x := F.mul P.X zi2
  let y := F.mul P.Y (F.mul zi2 zi)
  some (Bytes.ofList [if y % 2 == 1 then 3 else 2] ++ Bytes.ofNatBE 32 x)

/-- The public key matching a 32-byte big-endian secret scalar. -/
def publicKeyOfSecret (secret : Bytes) : Option Bytes := do
  if secret.size != 32 then none else
  let d := Bytes.toNatBE secret
  if d == 0 || d ≥ n then none else
  encodePoint (Point.smul d Point.base)

/-- The deterministic nonce of RFC 6979, using HMAC-SHA256. -/
def rfc6979Nonce (secret hash : Bytes) : Nat :=
  let h1 := hash
  let z := Bytes.toNatBE h1
  let z := if z ≥ n then z - n else z
  let bits2octets := Bytes.ofNatBE 32 z
  let v₀ := Bytes.ofList (List.replicate 32 0x01)
  let k₀ := Bytes.ofList (List.replicate 32 0x00)
  let k₁ := Hmac.sha256 k₀ (v₀ ++ Bytes.ofList [0x00] ++ secret ++ bits2octets)
  let v₁ := Hmac.sha256 k₁ v₀
  let k₂ := Hmac.sha256 k₁ (v₁ ++ Bytes.ofList [0x01] ++ secret ++ bits2octets)
  let v₂ := Hmac.sha256 k₂ v₁
  let rec go (k v : Bytes) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 1
    | fuel + 1 =>
      -- `t` is both the candidate and the new `V`
      let t := Hmac.sha256 k v
      let candidate := Bytes.toNatBE t
      if candidate ≥ 1 && candidate < n then candidate
      else
        let k' := Hmac.sha256 k (t ++ Bytes.ofList [0x00])
        go k' (Hmac.sha256 k' t) fuel
  go k₂ v₂ 32

/-- Sign a message with a 32-byte big-endian secret scalar, producing a DER
encoded low-`s` signature. -/
def sign (secret message : Bytes) : Option Bytes := do
  if secret.size != 32 then none else
  let d := Bytes.toNatBE secret
  if d == 0 || d ≥ n then none else
  let hash := Sha256.hash message
  let e := Bytes.toNatBE hash % n
  let k := rfc6979Nonce secret hash
  let point := Point.smul k Point.base
  let some x := point.affineX | none
  let r := x % n
  if r == 0 then none else
  let s := N.inv k * (e + r * d) % n
  if s == 0 then none else
  -- normalise to the low half, as the reference implementation does
  let s := if 2 * s > n then n - s else s
  some (Der.encodeSignature r s)

/-- Verify an ECDSA/SHA-256 signature over secp256r1. -/
def verify (publicKey message signature : Bytes) : Except Failure Unit := do
  let some (r, s) := Der.parseSignature signature | throw .badSignatureEncoding
  let some q := decodePublicKey publicKey | throw .badPoint
  if r == 0 || r ≥ n || s == 0 || s ≥ n then throw .outOfRange
  let e := Bytes.toNatBE (Sha256.hash message) % n
  let w := N.inv s
  let u₁ := e * w % n
  let u₂ := r * w % n
  let point := Point.add (Point.smul u₁ Point.base) (Point.smul u₂ q)
  let some x := point.affineX | throw .equation
  if x % n == r then pure () else throw .equation

end P256
end LeanBiscuit
