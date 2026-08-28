/-!
# Byte string helpers

Biscuit tokens are byte-oriented: protobuf payloads, signatures, public keys and
datalog `bytes` terms are all sequences of octets.  This module collects the
small amount of `ByteArray` plumbing the rest of the library needs.

Every function here is total and pure, so that the results can later be reasoned
about without having to model `IO` or partiality.
-/

namespace LeanBiscuit

/-- A byte string. -/
abbrev Bytes := ByteArray

namespace Bytes

/-- Empty byte string. -/
def empty : Bytes := ByteArray.empty

/-- Build a byte string from a list of bytes. -/
def ofList (l : List UInt8) : Bytes := ⟨l.toArray⟩

/-- Build a byte string from a list of natural numbers, truncating each to 8 bits. -/
def ofNatList (l : List Nat) : Bytes := ofList (l.map (fun n => UInt8.ofNat n))

/-- The UTF-8 encoding of a string, as a byte string. -/
def ofString (s : String) : Bytes := s.toUTF8

/-- Lexicographic comparison, shorter prefixes first. -/
def compare (a b : Bytes) : Ordering :=
  let rec go (i : Nat) : Ordering :=
    if _h : i < a.size ∧ i < b.size then
      match Ord.compare a[i]! b[i]! with
      | .eq => go (i + 1)
      | o => o
    else if i < a.size then .gt
    else if i < b.size then .lt
    else .eq
  termination_by a.size - i
  decreasing_by
    simp_wf
    omega
  go 0

instance : Ord Bytes := ⟨compare⟩

instance : Repr ByteArray where
  reprPrec b _ := repr b.toList

/-- Hexadecimal digit for a value below 16 (lowercase). -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'a'.toNat)

/-- Lowercase hexadecimal rendering, two characters per byte. -/
def toHex (b : Bytes) : String :=
  b.toList.foldl (fun acc c =>
    acc.push (hexDigit (c.toNat / 16)) |>.push (hexDigit (c.toNat % 16))) ""

/-- The numeric value of a hexadecimal digit, if it is one. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a lowercase or uppercase hexadecimal string.  Fails on odd length or
non-hex characters. -/
def ofHex? (s : String) : Option Bytes := do
  let cs := s.toList
  if cs.length % 2 != 0 then none else
  let rec go (l : List Char) (acc : Bytes) : Option Bytes :=
    match l with
    | [] => some acc
    | c₁ :: c₂ :: rest => do
      let h ← hexVal c₁
      let lo ← hexVal c₂
      go rest (acc.push (UInt8.ofNat (h * 16 + lo)))
    | _ => none
  go cs ByteArray.empty

/-- Big-endian interpretation of a byte string as a natural number. -/
def toNatBE (b : Bytes) : Nat :=
  b.toList.foldl (fun acc c => acc * 256 + c.toNat) 0

/-- Little-endian interpretation of a byte string as a natural number. -/
def toNatLE (b : Bytes) : Nat :=
  b.toList.reverse.foldl (fun acc c => acc * 256 + c.toNat) 0

/-- `n` rendered big-endian in exactly `len` bytes (truncating high bytes). -/
def ofNatBE (len : Nat) (n : Nat) : Bytes :=
  let rec go (i : Nat) (n : Nat) (acc : List UInt8) : List UInt8 :=
    match i with
    | 0 => acc
    | i + 1 => go i (n / 256) (UInt8.ofNat (n % 256) :: acc)
  ofList (go len n [])

/-- `n` rendered little-endian in exactly `len` bytes (truncating high bytes). -/
def ofNatLE (len : Nat) (n : Nat) : Bytes :=
  let rec go (i : Nat) (n : Nat) (acc : List UInt8) : List UInt8 :=
    match i with
    | 0 => acc.reverse
    | i + 1 => go i (n / 256) (UInt8.ofNat (n % 256) :: acc)
  ofList (go len n [])

/-- The little-endian 4-byte encoding of a 32 bit value, as used by the biscuit
signature payloads for algorithm identifiers and format versions. -/
def u32le (n : Nat) : Bytes := ofNatLE 4 n

/-- Concatenate a list of byte strings. -/
def concat (l : List Bytes) : Bytes := l.foldl (· ++ ·) ByteArray.empty

end Bytes

end LeanBiscuit
