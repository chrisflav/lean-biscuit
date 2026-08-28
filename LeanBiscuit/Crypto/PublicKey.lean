import LeanBiscuit.Crypto.Ed25519
import LeanBiscuit.Crypto.P256
import LeanBiscuit.Error

/-!
# Public keys and signature verification

Biscuit supports several signature algorithms, and the algorithm may change from
block to block within a single token.  This module wraps the concrete
implementations behind one type.
-/

namespace LeanBiscuit

/-- A signature algorithm, numbered as in the protobuf `PublicKey.Algorithm`
enum. -/
inductive Algorithm where
  /-- Ed25519, as specified in RFC 8032.  This is the default. -/
  | ed25519
  /-- ECDSA over secp256r1 with SHA-256. -/
  | secp256r1
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Algorithm

/-- The numeric tag used by the protobuf encoding and by the signature
payloads. -/
def toNat : Algorithm → Nat
  | .ed25519 => 0
  | .secp256r1 => 1

/-- The algorithm for a protobuf tag, if it is known. -/
def ofNat? : Nat → Option Algorithm
  | 0 => some .ed25519
  | 1 => some .secp256r1
  | _ => none

/-- The prefix used when printing a public key in datalog source. -/
def name : Algorithm → String
  | .ed25519 => "ed25519"
  | .secp256r1 => "secp256r1"

end Algorithm

/-- A public key: an algorithm together with its algorithm-specific encoding
(compressed Edwards `y` for Ed25519, compressed SEC1 for secp256r1). -/
structure PublicKey where
  /-- The signature algorithm this key is for. -/
  algorithm : Algorithm
  /-- The serialized key material. -/
  key : Bytes
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PublicKey

/-- The datalog source rendering of a key, e.g. `ed25519/0123…`. -/
def print (k : PublicKey) : String := s!"{k.algorithm.name}/{Bytes.toHex k.key}"

/-- Ordering by algorithm then by key material; used to keep key tables in a
deterministic order. -/
def compare (a b : PublicKey) : Ordering :=
  match Ord.compare a.algorithm.toNat b.algorithm.toNat with
  | .eq => Bytes.compare a.key b.key
  | o => o

/-- The message string the reference implementation reports when a signature
does not satisfy the verification equation. -/
def verificationFailureMessage : String :=
  "signature error: Verification equation was not satisfied"

/-- Verify `signature` over `message` under this key. -/
def verifySignature (k : PublicKey) (message signature : Bytes) : Except FormatError Unit :=
  match k.algorithm with
  | .ed25519 =>
    if signature.size != 64 then
      -- the reference implementation reports the raw bytes it could not convert
      throw (.blockSignatureDeserializationError
        s!"block signature deserialization error: {reprStr signature.toList}")
    else
      match Ed25519.verify k.key message signature with
      | .ok _ => pure ()
      | .error _ => throw (.signature (.invalidSignature verificationFailureMessage))
  | .secp256r1 =>
    match P256.Der.parseSignature signature with
    | none =>
      throw (.blockSignatureDeserializationError
        s!"block signature deserialization error: {reprStr signature.toList}")
    | some _ =>
      match P256.verify k.key message signature with
      | .ok _ => pure ()
      | .error _ => throw (.signature (.invalidSignature verificationFailureMessage))

/-- Parse a public key of the given algorithm from its serialized form. -/
def ofBytes (algorithm : Algorithm) (bytes : Bytes) : Except FormatError PublicKey :=
  match algorithm with
  | .ed25519 =>
    if bytes.size != 32 then throw (.invalidKeySize bytes.size)
    else pure ⟨.ed25519, bytes⟩
  | .secp256r1 =>
    if bytes.size != 33 then throw (.invalidKeySize bytes.size)
    else pure ⟨.secp256r1, bytes⟩

end PublicKey

end LeanBiscuit
