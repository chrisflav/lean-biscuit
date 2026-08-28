import LeanBiscuit.Crypto.PublicKey

/-!
# Private keys

A token creator holds a private key; every attenuation generates an ephemeral
key pair whose secret is carried in the token so that the holder can sign one
more block.  Both supported algorithms are covered here.
-/

namespace LeanBiscuit

/-- A private key: an algorithm together with its serialized scalar. -/
structure PrivateKey where
  /-- The signature algorithm this key is for. -/
  algorithm : Algorithm
  /-- The serialized secret: 32 random bytes for Ed25519, the big-endian secret
  scalar for secp256r1. -/
  key : Bytes
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PrivateKey

/-- Parse a private key, checking its length. -/
def ofBytes (algorithm : Algorithm) (bytes : Bytes) : Except FormatError PrivateKey :=
  if bytes.size != 32 then throw (.invalidKeySize bytes.size)
  else pure ⟨algorithm, bytes⟩

/-- The matching public key. -/
def publicKey (k : PrivateKey) : Except FormatError PublicKey :=
  match k.algorithm with
  | .ed25519 =>
    match Ed25519.publicKeyOfSecret k.key with
    | some b => pure ⟨.ed25519, b⟩
    | none => throw (.invalidKey "invalid Ed25519 private key")
  | .secp256r1 =>
    match P256.publicKeyOfSecret k.key with
    | some b => pure ⟨.secp256r1, b⟩
    | none => throw (.invalidKey "invalid secp256r1 private key")

/-- Sign a message. -/
def sign (k : PrivateKey) (message : Bytes) : Except FormatError Bytes :=
  match k.algorithm with
  | .ed25519 =>
    match Ed25519.sign k.key message with
    | some s => pure s
    | none => throw (.signature (.invalidSignatureGeneration "invalid Ed25519 private key"))
  | .secp256r1 =>
    match P256.sign k.key message with
    | some s => pure s
    | none => throw (.signature (.invalidSignatureGeneration "invalid secp256r1 private key"))

end PrivateKey

end LeanBiscuit
