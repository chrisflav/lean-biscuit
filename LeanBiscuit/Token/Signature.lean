import LeanBiscuit.Proto.Schema

/-!
# Signature payloads

What exactly a block signature covers is the security-critical part of the
format: it is what binds a block to its position in the chain and prevents a
block from being moved, reordered or reused in another token.

Two payload formats exist.  Version 0 covers only the block's own data and the
next public key.  Version 1 additionally covers the previous signature — which
is what pins a block to one specific token — and tags every component with a
label so that no two different structures can produce the same byte string.
-/

namespace LeanBiscuit
namespace Token

open Proto

/-- The little-endian four byte encoding of an algorithm identifier. -/
def algorithmBytes (k : PublicKey) : Bytes := Bytes.u32le k.algorithm.toNat

/-- The block signature payload, version 0.

Deprecated: it does not cover the previous signature, so a third-party block
signed under it could be replayed into another token. -/
def blockSignaturePayloadV0 (data : Bytes) (nextKey : PublicKey)
    (externalSignature : Option ExternalSignature) : Bytes :=
  data
    ++ (match externalSignature with
        | none => Bytes.empty
        | some e => e.signature)
    ++ algorithmBytes nextKey
    ++ nextKey.key

/-- The block signature payload, version 1. -/
def blockSignaturePayloadV1 (data : Bytes) (nextKey : PublicKey)
    (externalSignature : Option ExternalSignature) (previousSignature : Bytes)
    (version : Nat) : Bytes :=
  Bytes.ofString "\x00BLOCK\x00\x00VERSION\x00"
    ++ Bytes.u32le version
    ++ Bytes.ofString "\x00PAYLOAD\x00" ++ data
    ++ Bytes.ofString "\x00ALGORITHM\x00" ++ algorithmBytes nextKey
    ++ Bytes.ofString "\x00NEXTKEY\x00" ++ nextKey.key
    ++ Bytes.ofString "\x00PREVSIG\x00" ++ previousSignature
    ++ (match externalSignature with
        | none => Bytes.empty
        | some e => Bytes.ofString "\x00EXTERNALSIG\x00" ++ e.signature)

/-- The authority block signature payload, version 1.

The authority block has no previous signature to cover, and must not carry an
external signature. -/
def authorityBlockSignaturePayloadV1 (data : Bytes) (nextKey : PublicKey) (version : Nat) :
    Bytes :=
  Bytes.ofString "\x00BLOCK\x00\x00VERSION\x00"
    ++ Bytes.u32le version
    ++ Bytes.ofString "\x00PAYLOAD\x00" ++ data
    ++ Bytes.ofString "\x00ALGORITHM\x00" ++ algorithmBytes nextKey
    ++ Bytes.ofString "\x00NEXTKEY\x00" ++ nextKey.key

/-- The external signature payload, version 0.  No longer supported for
verification of new tokens. -/
def externalSignaturePayloadV0 (data : Bytes) (previousKey : PublicKey) : Bytes :=
  data ++ algorithmBytes previousKey ++ previousKey.key

/-- The external signature payload, version 1.

Covering the previous signature is what makes a third-party block usable in
exactly one token. -/
def externalSignaturePayloadV1 (data previousSignature : Bytes) (version : Nat) : Bytes :=
  Bytes.ofString "\x00EXTERNAL\x00\x00VERSION\x00"
    ++ Bytes.u32le version
    ++ Bytes.ofString "\x00PAYLOAD\x00" ++ data
    ++ Bytes.ofString "\x00PREVSIG\x00" ++ previousSignature

/-- The payload a seal signs: the last block together with its own signature, so
that no further block can be appended. -/
def sealSignaturePayloadV0 (b : SignedBlock) : Bytes :=
  b.block ++ algorithmBytes b.nextKey ++ b.nextKey.key ++ b.signature

/-- The signature payload format version that third-party blocks must use. -/
def thirdPartySignatureVersion : Nat := 1

end Token
end LeanBiscuit
