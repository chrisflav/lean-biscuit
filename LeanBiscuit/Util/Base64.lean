import LeanBiscuit.Util.Bytes

/-!
# URL-safe base64

The specification says that a biscuit token transmitted as text is encoded with
URL-safe base64 (alphabet `A-Za-z0-9-_`).  The reference implementation uses the
padded variant, and accepts input with or without padding.
-/

namespace LeanBiscuit
namespace Base64

/-- The URL-safe base64 alphabet. -/
def alphabet : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

/-- The 6-bit value of a base64 character, if it is one. -/
def decodeChar (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '-' then some 62
  else if c == '_' then some 63
  else none

/-- The base64 character for a 6-bit value. -/
def encodeChar (n : Nat) : Char := alphabet.toList.getD n 'A'

/-- URL-safe base64 encoding, with `=` padding. -/
def encode (b : Bytes) : String :=
  let rec go (l : List UInt8) (acc : String) : String :=
    match l with
    | [] => acc
    | [x] =>
      let n := x.toNat
      acc.push (encodeChar (n >>> 2)) |>.push (encodeChar ((n &&& 3) <<< 4))
        |>.push '=' |>.push '='
    | [x, y] =>
      let n := x.toNat * 256 + y.toNat
      acc.push (encodeChar (n >>> 10)) |>.push (encodeChar ((n >>> 4) &&& 63))
        |>.push (encodeChar ((n &&& 15) <<< 2)) |>.push '='
    | x :: y :: z :: rest =>
      let n := (x.toNat * 256 + y.toNat) * 256 + z.toNat
      go rest (acc.push (encodeChar (n >>> 18)) |>.push (encodeChar ((n >>> 12) &&& 63))
        |>.push (encodeChar ((n >>> 6) &&& 63)) |>.push (encodeChar (n &&& 63)))
  go b.toList ""

/-- URL-safe base64 decoding.  Padding is optional; any invalid character makes
decoding fail. -/
def decode? (s : String) : Option Bytes :=
  let chars := s.toList.filter (· != '=')
  let rec go (l : List Char) (acc : Bytes) : Option Bytes :=
    match l with
    | [] => some acc
    | [_] => none
    | [a, b] => do
      let a ← decodeChar a
      let b ← decodeChar b
      if b &&& 15 != 0 then none else
      some (acc.push (UInt8.ofNat ((a <<< 2) ||| (b >>> 4))))
    | [a, b, c] => do
      let a ← decodeChar a
      let b ← decodeChar b
      let c ← decodeChar c
      if c &&& 3 != 0 then none else
      some (acc.push (UInt8.ofNat ((a <<< 2) ||| (b >>> 4)))
              |>.push (UInt8.ofNat (((b &&& 15) <<< 4) ||| (c >>> 2))))
    | a :: b :: c :: d :: rest => do
      let a ← decodeChar a
      let b ← decodeChar b
      let c ← decodeChar c
      let d ← decodeChar d
      go rest (acc.push (UInt8.ofNat ((a <<< 2) ||| (b >>> 4)))
                 |>.push (UInt8.ofNat (((b &&& 15) <<< 4) ||| (c >>> 2)))
                 |>.push (UInt8.ofNat (((c &&& 3) <<< 6) ||| d)))
  go chars ByteArray.empty

end Base64
end LeanBiscuit
