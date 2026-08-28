import LeanBiscuit.Proto.Wire
import LeanBiscuit.Crypto.PublicKey

/-!
# The biscuit container format

The outer protobuf messages: the token envelope, its signed blocks, and the
proof that terminates the signature chain.  The datalog payload of a block is
itself a protobuf message, decoded separately in `LeanBiscuit.Token.Block`,
because it must be kept as raw bytes here: those exact bytes are what the
signatures cover.
-/

namespace LeanBiscuit
namespace Proto

open Wire

/-- A signature by a third party over a block's contents. -/
structure ExternalSignature where
  /-- The signature. -/
  signature : Bytes
  /-- The key that produced it. -/
  publicKey : PublicKey
  deriving Repr, Inhabited

/-- One link of the signature chain. -/
structure SignedBlock where
  /-- The serialized datalog block; the signature covers these exact bytes. -/
  block : Bytes
  /-- The public key the next block will be signed with. -/
  nextKey : PublicKey
  /-- The signature by the previous key. -/
  signature : Bytes
  /-- A third party's signature over this block, if any. -/
  externalSignature : Option ExternalSignature := none
  /-- The version of the signature payload format; absent means version 0. -/
  version : Nat := 0
  deriving Repr, Inhabited

/-- What terminates the signature chain. -/
inductive Proof where
  /-- The secret matching the last block's `nextKey`: the token can still be
  attenuated. -/
  | secret (nextSecret : Bytes)
  /-- A signature over the last block: the token is sealed. -/
  | seal (finalSignature : Bytes)
  deriving Repr, Inhabited

/-- A token as it travels on the wire. -/
structure Biscuit where
  /-- A hint about which root key to verify with. -/
  rootKeyId : Option Nat := none
  /-- The authority block, which grants the token's rights. -/
  authority : SignedBlock
  /-- The attenuating blocks, in order. -/
  blocks : List SignedBlock := []
  /-- The end of the signature chain. -/
  proof : Proof
  deriving Repr, Inhabited

/-- The context a third party needs in order to sign a block for a token. -/
structure ThirdPartyBlockRequest where
  /-- The signature of the token's last block. -/
  previousSignature : Bytes
  deriving Repr, Inhabited

/-- What a third party returns: a serialized block and its signature. -/
structure ThirdPartyBlockContents where
  /-- The serialized datalog block. -/
  payload : Bytes
  /-- The third party's signature over it. -/
  externalSignature : ExternalSignature
  deriving Repr, Inhabited

namespace Schema

/-- Report a malformed container. -/
def fail (message : String) : Except FormatError α :=
  throw (.deserializationError s!"deserialization error: {message}")

/-- Decode a `PublicKey` message. -/
def decodePublicKey (f : Fields) : Except FormatError PublicKey := do
  let some alg := uint? f 1 | fail "missing public key algorithm"
  let some algorithm := Algorithm.ofNat? alg | fail s!"unknown public key algorithm {alg}"
  let some key := bytes? f 2 | fail "missing public key bytes"
  PublicKey.ofBytes algorithm key

/-- Decode an `ExternalSignature` message. -/
def decodeExternalSignature (f : Fields) : Except FormatError ExternalSignature := do
  let some signature := bytes? f 1 | fail "missing external signature"
  let .ok (some keyFields) := message? f 2 | fail "missing external signature public key"
  pure ⟨signature, ← decodePublicKey keyFields⟩

/-- Decode a `SignedBlock` message. -/
def decodeSignedBlock (f : Fields) : Except FormatError SignedBlock := do
  let some block := bytes? f 1 | fail "missing block payload"
  let .ok (some keyFields) := message? f 2 | fail "missing next key"
  let nextKey ← decodePublicKey keyFields
  let some signature := bytes? f 3 | fail "missing block signature"
  let externalSignature ←
    match ← liftM (message? f 4 |>.mapError (fun e => FormatError.deserializationError e)) with
    | none => pure none
    | some ef => do pure (some (← decodeExternalSignature ef))
  pure { block, nextKey, signature, externalSignature, version := (uint? f 5).getD 0 }

/-- Decode a `Proof` message. -/
def decodeProof (f : Fields) : Except FormatError Proof := do
  match bytes? f 1, bytes? f 2 with
  | some secret, _ => pure (.secret secret)
  | none, some sig => pure (.seal sig)
  | none, none => throw (.deserializationError "could not find proof")

/-- Decode a whole token. -/
def decodeBiscuit (data : Bytes) : Except FormatError Biscuit := do
  let .ok f := Wire.decode data | fail "could not decode the token envelope"
  let .ok (some authorityFields) := message? f 2 | fail "missing authority block"
  let authority ← decodeSignedBlock authorityFields
  let .ok blockFields := allMessages f 3 | fail "could not decode a block"
  let blocks ← blockFields.mapM decodeSignedBlock
  let .ok (some proofFields) := message? f 4 | fail "missing proof"
  let proof ← decodeProof proofFields
  pure { rootKeyId := uint? f 1, authority, blocks, proof }

/-- Decode a `ThirdPartyBlockRequest`. -/
def decodeThirdPartyBlockRequest (data : Bytes) : Except FormatError ThirdPartyBlockRequest := do
  let .ok f := Wire.decode data | fail "could not decode the third-party block request"
  if !(allBytes f 1).isEmpty then
    fail "the third-party block request must not carry a legacy previous key"
  if !(allBytes f 2).isEmpty then
    fail "the third-party block request must not carry legacy public keys"
  let some previousSignature := bytes? f 3 | fail "missing previous signature"
  pure ⟨previousSignature⟩

/-- Decode a `ThirdPartyBlockContents`. -/
def decodeThirdPartyBlockContents (data : Bytes) : Except FormatError ThirdPartyBlockContents := do
  let .ok f := Wire.decode data | fail "could not decode the third-party block contents"
  let some payload := bytes? f 1 | fail "missing third-party block payload"
  let .ok (some sigFields) := message? f 2 | fail "missing third-party external signature"
  pure ⟨payload, ← decodeExternalSignature sigFields⟩

/-- Encode a `PublicKey` message. -/
def encodePublicKey (k : PublicKey) : Bytes :=
  encodeUint 1 k.algorithm.toNat ++ encodeBytes 2 k.key

/-- Encode an `ExternalSignature` message. -/
def encodeExternalSignature (e : ExternalSignature) : Bytes :=
  encodeBytes 1 e.signature ++ encodeBytes 2 (encodePublicKey e.publicKey)

/-- Encode a `SignedBlock` message. -/
def encodeSignedBlock (b : SignedBlock) : Bytes :=
  encodeBytes 1 b.block
    ++ encodeBytes 2 (encodePublicKey b.nextKey)
    ++ encodeBytes 3 b.signature
    ++ (match b.externalSignature with
        | none => Bytes.empty
        | some e => encodeBytes 4 (encodeExternalSignature e))
    ++ (if b.version > 0 then encodeUint 5 b.version else Bytes.empty)

/-- Encode a `Proof` message. -/
def encodeProof : Proof → Bytes
  | .secret s => encodeBytes 1 s
  | .seal s => encodeBytes 2 s

/-- Encode a whole token. -/
def encodeBiscuit (b : Biscuit) : Bytes :=
  (match b.rootKeyId with
   | none => Bytes.empty
   | some id => encodeUint 1 id)
    ++ encodeBytes 2 (encodeSignedBlock b.authority)
    ++ Bytes.concat (b.blocks.map fun x => encodeBytes 3 (encodeSignedBlock x))
    ++ encodeBytes 4 (encodeProof b.proof)

/-- Encode a `ThirdPartyBlockRequest`. -/
def encodeThirdPartyBlockRequest (r : ThirdPartyBlockRequest) : Bytes :=
  encodeBytes 3 r.previousSignature

/-- Encode a `ThirdPartyBlockContents`. -/
def encodeThirdPartyBlockContents (c : ThirdPartyBlockContents) : Bytes :=
  encodeBytes 1 c.payload ++ encodeBytes 2 (encodeExternalSignature c.externalSignature)

end Schema
end Proto
end LeanBiscuit
