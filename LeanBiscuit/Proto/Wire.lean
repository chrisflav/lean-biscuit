import LeanBiscuit.Util.Bytes

/-!
# Protocol Buffers wire format

Biscuit tokens are serialized with proto2.  Only the wire format is modelled
here: a message is decoded into a flat list of `(field number, value)` pairs,
and the schema-specific modules in `LeanBiscuit.Proto.Schema` interpret those.

Keeping the two layers apart means the wire decoder can be specified and
verified on its own, independently of the biscuit schema.
-/

namespace LeanBiscuit
namespace Proto

/-- A value as it appears on the wire, before schema interpretation. -/
inductive WireValue where
  /-- Wire type 0: a base-128 varint. -/
  | varint (value : Nat)
  /-- Wire type 1: eight bytes, little-endian. -/
  | fixed64 (value : Nat)
  /-- Wire type 2: a length-delimited byte string. -/
  | bytes (value : Bytes)
  /-- Wire type 5: four bytes, little-endian. -/
  | fixed32 (value : Nat)
  deriving Repr, Inhabited

/-- A decoded message: the fields in the order they appeared. -/
abbrev Fields := List (Nat × WireValue)

namespace Wire

/-- Read a base-128 varint starting at `i`.  Returns the value and the offset
just past it. -/
def readVarint (b : Bytes) (i : Nat) : Except String (Nat × Nat) :=
  let rec go (i shift acc fuel : Nat) : Except String (Nat × Nat) :=
    match fuel with
    | 0 => throw "varint is too long"
    | fuel + 1 =>
      if i ≥ b.size then throw "unexpected end of input while reading a varint"
      else
        let byte := (b[i]!).toNat
        let acc := acc + (byte % 128) * 2 ^ shift
        if byte < 128 then pure (acc, i + 1)
        else go (i + 1) (shift + 7) acc fuel
  go i 0 0 10

/-- Read `n` little-endian bytes starting at `i` as a natural number. -/
def readFixed (b : Bytes) (i n : Nat) : Except String (Nat × Nat) :=
  if i + n > b.size then throw "unexpected end of input while reading a fixed-width field"
  else pure (Bytes.toNatLE (b.extract i (i + n)), i + n)

/-- Read the value of a field with the given wire type, starting at `i`.
Returns the value and the offset just past it. -/
def readValue (b : Bytes) (i wireType : Nat) : Except String (WireValue × Nat) :=
  match wireType with
  | 0 => do let (v, j) ← readVarint b i; pure (.varint v, j)
  | 1 => do let (v, j) ← readFixed b i 8; pure (.fixed64 v, j)
  | 2 => do
    let (len, j) ← readVarint b i
    if j + len > b.size then throw "length-delimited field runs past the end of the message"
    else pure (.bytes (b.extract j (j + len)), j + len)
  | 5 => do let (v, j) ← readFixed b i 4; pure (.fixed32 v, j)
  | 3 | 4 => throw "groups are not supported"
  | w => throw s!"unknown wire type {w}"

/-- Decode fields starting at offset `i`, accumulating them in reverse. -/
def decodeAux (b : Bytes) (i : Nat) (acc : Fields) : Except String Fields :=
  if _h : i < b.size then
    match readVarint b i with
    | .error e => .error e
    | .ok (key, i₁) =>
      let fieldNumber := key / 8
      if fieldNumber == 0 then .error "invalid field number 0"
      else
        match readValue b i₁ (key % 8) with
        | .error e => .error e
        | .ok (v, next) =>
          if _h₂ : i < next then decodeAux b next ((fieldNumber, v) :: acc)
          else .error "protobuf decoding made no progress"
  else .ok acc.reverse
termination_by b.size - i
decreasing_by omega

/-- Decode a whole message into its fields. -/
def decode (b : Bytes) : Except String Fields := decodeAux b 0 []

/-- All values for a field number, in order. -/
def all (f : Fields) (n : Nat) : List WireValue :=
  f.filterMap (fun (k, v) => if k == n then some v else none)

/-- The value of a singular field: proto2 says the last one wins. -/
def last? (f : Fields) (n : Nat) : Option WireValue := (all f n).getLast?

/-- The `uint64`/`uint32`/`bool`/enum interpretation of a singular field. -/
def uint? (f : Fields) (n : Nat) : Option Nat :=
  match last? f n with
  | some (.varint v) => some v
  | some (.fixed32 v) => some v
  | some (.fixed64 v) => some v
  | _ => none

/-- The `int64` interpretation of a singular field: a varint holding a two's
complement 64 bit value. -/
def int? (f : Fields) (n : Nat) : Option Int :=
  (uint? f n).map fun v =>
    let w : Nat := v % 2 ^ 64
    if w ≥ 2 ^ 63 then (w : Int) - (2 : Int) ^ 64 else (w : Int)

/-- The `bool` interpretation of a singular field. -/
def bool? (f : Fields) (n : Nat) : Option Bool := (uint? f n).map (· != 0)

/-- The `bytes` interpretation of a singular field. -/
def bytes? (f : Fields) (n : Nat) : Option Bytes :=
  match last? f n with
  | some (.bytes v) => some v
  | _ => none

/-- The `string` interpretation of a singular field.  Invalid UTF-8 is replaced
character by character, matching the lenience of the reference implementations'
protobuf readers on already-validated tokens. -/
def string? (f : Fields) (n : Nat) : Option String :=
  (bytes? f n).map fun b => String.fromUTF8! b

/-- All length-delimited values of a repeated field. -/
def allBytes (f : Fields) (n : Nat) : List Bytes :=
  (all f n).filterMap fun
    | .bytes v => some v
    | _ => none

/-- All submessages of a repeated message field, decoded. -/
def allMessages (f : Fields) (n : Nat) : Except String (List Fields) :=
  (allBytes f n).mapM decode

/-- A singular submessage field, decoded. -/
def message? (f : Fields) (n : Nat) : Except String (Option Fields) :=
  match bytes? f n with
  | none => pure none
  | some b => do pure (some (← decode b))

/-- All string values of a repeated field. -/
def allStrings (f : Fields) (n : Nat) : List String :=
  (allBytes f n).map (fun b => String.fromUTF8! b)

/-- Encode a natural number as a base-128 varint. -/
def encodeVarint (n : Nat) : Bytes :=
  let rec go (n : Nat) (acc : Bytes) : Bytes :=
    if n < 128 then acc.push (UInt8.ofNat n)
    else go (n / 128) (acc.push (UInt8.ofNat (n % 128 + 128)))
  termination_by n
  decreasing_by omega
  go n ByteArray.empty

/-- The tag byte(s) for a field number and wire type. -/
def encodeKey (fieldNumber wireType : Nat) : Bytes := encodeVarint (fieldNumber * 8 + wireType)

/-- Encode a `uint64`-like field. -/
def encodeUint (fieldNumber n : Nat) : Bytes := encodeKey fieldNumber 0 ++ encodeVarint n

/-- Encode an `int64` field, using the two's complement representation. -/
def encodeInt (fieldNumber : Nat) (i : Int) : Bytes :=
  let v := if i < 0 then (2 ^ 64 + i).toNat else i.toNat
  encodeUint fieldNumber v

/-- Encode a `bool` field. -/
def encodeBool (fieldNumber : Nat) (b : Bool) : Bytes :=
  encodeUint fieldNumber (if b then 1 else 0)

/-- Encode a length-delimited field. -/
def encodeBytes (fieldNumber : Nat) (b : Bytes) : Bytes :=
  encodeKey fieldNumber 2 ++ encodeVarint b.size ++ b

/-- Encode a `string` field. -/
def encodeString (fieldNumber : Nat) (s : String) : Bytes := encodeBytes fieldNumber s.toUTF8

end Wire
end Proto
end LeanBiscuit
