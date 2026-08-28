import LeanBiscuit.Token.Block
import LeanBiscuit.Token.Signature
import LeanBiscuit.Crypto.PrivateKey
import LeanBiscuit.Util.Base64

/-!
# Tokens

A verified token: its signature chain has been checked against a root public
key, its blocks have been decoded, and its symbol table has been assembled.

The signature chain is what makes offline attenuation safe.  Each block is
signed by the key whose secret the previous holder had, and the token carries
the secret for the *next* block, so anyone can append — but nobody can remove or
alter a block without invalidating everything that follows.
-/

namespace LeanBiscuit
namespace Token

open Datalog Proto

/-- A token whose signatures have been verified. -/
structure Biscuit where
  /-- The container as it appeared on the wire; the raw block bytes are kept
  because they are what the signatures cover. -/
  container : Proto.Biscuit
  /-- The hint about which root key verifies this token. -/
  rootKeyId : Option Nat := none
  /-- The token-wide symbol table: the default symbols, then each non
  third-party block's symbols in order. -/
  symbols : SymbolTable := {}
  /-- The decoded blocks, the authority block first. -/
  blocks : List Block := []
  deriving Repr, Inhabited

namespace Biscuit

/-- The signed blocks in order, the authority block first. -/
def signedBlocks (c : Proto.Biscuit) : List SignedBlock := c.authority :: c.blocks

/-- Check the structural constraints the container must satisfy before its
signatures can be verified. -/
def checkContainer (c : Proto.Biscuit) : Except FormatError Unit := do
  if c.authority.externalSignature.isSome then
    throw (.deserializationError "the authority block must not contain an external signature")
  for b in c.blocks do
    if b.externalSignature.isSome && b.version != thirdPartySignatureVersion then
      throw (.deserializationError "Unsupported third party block version")

/-- Verify one block's signature, and the third party's signature if present. -/
def verifyBlock (b : SignedBlock) (key : PublicKey) (previousSignature : Bytes) :
    Except FormatError Unit := do
  let payload ←
    match b.version with
    | 0 => pure (blockSignaturePayloadV0 b.block b.nextKey b.externalSignature)
    | 1 => pure (blockSignaturePayloadV1 b.block b.nextKey b.externalSignature
                   previousSignature b.version)
    | v => throw (.deserializationError s!"unsupported block version: {v}")
  key.verifySignature payload b.signature
  match b.externalSignature with
  | none => pure ()
  | some e =>
    e.publicKey.verifySignature
      (externalSignaturePayloadV1 b.block previousSignature b.version) e.signature

/-- Verify the authority block's signature under the root key. -/
def verifyAuthorityBlock (b : SignedBlock) (root : PublicKey) : Except FormatError Unit := do
  let payload ←
    match b.version with
    | 0 => pure (blockSignaturePayloadV0 b.block b.nextKey b.externalSignature)
    | 1 => pure (authorityBlockSignaturePayloadV1 b.block b.nextKey b.version)
    | v => throw (.deserializationError s!"unsupported block version: {v}")
  root.verifySignature payload b.signature

/-- Verify the whole signature chain, ending with the proof.

An attenuable token proves it by carrying the secret matching the last public
key; a sealed token proves it by signing the last block with that secret, which
leaves nobody able to append. -/
def verifyChain (c : Proto.Biscuit) (root : PublicKey) : Except FormatError Unit := do
  verifyAuthorityBlock c.authority root
  let mut currentKey := c.authority.nextKey
  let mut previousSignature := c.authority.signature
  for b in c.blocks do
    verifyBlock b currentKey previousSignature
    currentKey := b.nextKey
    previousSignature := b.signature
  match c.proof with
  | .secret secret =>
    let secretKey ← PrivateKey.ofBytes currentKey.algorithm secret
    let derived ← secretKey.publicKey
    if derived != currentKey then
      throw (.signature (.invalidSignature "the last public key does not match the private key"))
  | .seal signature =>
    let last := match c.blocks.getLast? with
      | some b => b
      | none => c.authority
    currentKey.verifySignature (sealSignaturePayloadV0 last) signature

/-- Assemble the token-wide symbol table.

Third-party blocks are skipped: they are written by someone who does not have
the token, so they start from the default table and their symbols stay
local. -/
def buildSymbols (blocks : List Block) : Except FormatError SymbolTable := do
  let mut symbols : SymbolTable := {}
  for b in blocks do
    if b.externalKey.isNone then
      symbols ← symbols.extendSymbols b.symbols
      for k in b.publicKeys do
        let (_, t) ← symbols.insertKeyFallible k
        symbols := t
  pure symbols

/-- Decode the container and check the constraints that do not need a key. -/
def decodeContainer (data : Bytes) : Except TokenError Proto.Biscuit := do
  let container ← liftM (Schema.decodeBiscuit data |>.mapError TokenError.format)
  liftM (checkContainer container |>.mapError TokenError.format)
  -- the proof's secret must be a well formed key for the last block's algorithm
  let lastKey := (signedBlocks container).getLast!.nextKey
  match container.proof with
  | .secret secret =>
    let _ ← liftM ((PrivateKey.ofBytes lastKey.algorithm secret).mapError TokenError.format)
    pure ()
  | .seal _ => pure ()
  pure container

/-- Decode a container's blocks and assemble its symbol table. -/
def decodeBlocks (container : Proto.Biscuit) : Except TokenError Biscuit := do
  let blocks ← liftM (((signedBlocks container).mapM fun b =>
    decodeBlock b.block (b.externalSignature.map (·.publicKey))).mapError TokenError.format)
  let symbols ← liftM (buildSymbols blocks |>.mapError TokenError.format)
  pure { container, rootKeyId := container.rootKeyId, symbols, blocks }

/-- Decode a token and verify it against whichever root key its `rootKeyId`
selects.

A deployment that rotates root keys publishes several; the token names which one
it was signed with, and the provider decides whether that choice is
acceptable. -/
def ofBytesWith (data : Bytes) (chooseRoot : Option Nat → Except FormatError PublicKey) :
    Except TokenError Biscuit := do
  let container ← decodeContainer data
  let root ← liftM ((chooseRoot container.rootKeyId).mapError TokenError.format)
  liftM (verifyChain container root |>.mapError TokenError.format)
  decodeBlocks container

/-- Decode and verify a token against a root public key. -/
def ofBytes (data : Bytes) (root : PublicKey) : Except TokenError Biscuit :=
  ofBytesWith data (fun _ => pure root)

/-- Decode a token without verifying its signatures.

Useful for tooling that inspects a token it cannot verify — but the contents
must not be trusted, since anyone can produce them. -/
def ofBytesUnverified (data : Bytes) : Except TokenError Biscuit := do
  decodeBlocks (← decodeContainer data)

/-- Decode and verify a token from its URL-safe base64 text form. -/
def ofBase64 (s : String) (root : PublicKey) : Except TokenError Biscuit := do
  let s := if s.startsWith "biscuit:" then s.dropPrefix? "biscuit:" |>.get!.toString else s
  match Base64.decode? s with
  | none => throw (.base64 "Invalid base64 token")
  | some data => ofBytes data root

/-- The number of blocks, which is at least one. -/
def blockCount (b : Biscuit) : Nat := b.blocks.length

/-- The revocation identifier of each block, in order.

A block's signature identifies it uniquely, so publishing it revokes exactly the
tokens that contain that block and everything derived from them. -/
def revocationIdentifiers (b : Biscuit) : List Bytes :=
  (signedBlocks b.container).map (·.signature)

/-- The external key of each block, in order; `none` for first-party blocks. -/
def externalKeys (b : Biscuit) : List (Option PublicKey) :=
  (signedBlocks b.container).map fun sb => sb.externalSignature.map (·.publicKey)

/-- Is the token sealed against further attenuation? -/
def isSealed (b : Biscuit) : Bool :=
  match b.container.proof with
  | .seal _ => true
  | .secret _ => false

/-- Serialize the token. -/
def toBytes (b : Biscuit) : Bytes := Schema.encodeBiscuit b.container

/-- Serialize the token to its URL-safe base64 text form. -/
def toBase64 (b : Biscuit) : String := Base64.encode (toBytes b)

end Biscuit

end Token
end LeanBiscuit
