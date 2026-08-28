import LeanBiscuit.Token.Biscuit
import LeanBiscuit.Parser

/-!
# Creating and attenuating tokens

The other half of the specification: minting a token, adding a block to one, and
sealing it.

Attenuation is the point of the format.  A token carries the secret matching the
public key its last block names, so whoever holds it can sign one more block —
and only append, since every block's signature covers the previous one.  That
ephemeral key pair is meant to be forgotten as soon as it has been used.
-/

namespace LeanBiscuit
namespace Token

open Datalog Proto

/-- The contents of a block, before it is interned and signed. -/
structure BlockBuilder where
  /-- Facts the block states. -/
  facts : List Builder.Fact := []
  /-- Rules the block defines. -/
  rules : List Builder.Rule := []
  /-- Checks the block imposes. -/
  checks : List Builder.Check := []
  /-- The block-level trust annotation. -/
  scopes : List Builder.Scope := []
  /-- Free-form context. -/
  context : Option String := none
  deriving Inhabited

namespace BlockBuilder

/-- Add the contents of a datalog source string. -/
def code (b : BlockBuilder) (source : String) : Except TokenError BlockBuilder :=
  match Parser.parseBlock source with
  | .error e => throw (.language e)
  | .ok r =>
    pure { b with
      facts := b.facts ++ r.facts,
      rules := b.rules ++ r.rules,
      checks := b.checks ++ r.checks,
      scopes := b.scopes ++ r.scopes }

/-- Intern the block's contents on top of `baseSymbols`.

The block's own symbol table is what interning *added*: everything the base
table already had is referred to by index and does not travel with the block. -/
def build (b : BlockBuilder) (baseSymbols : SymbolTable) : Block :=
  let symbolStart := baseSymbols.symbols.size
  let keyStart := baseSymbols.publicKeys.size
  let (facts, symbols) := b.facts.foldl (fun (acc, t) f =>
    let (f, t) := Builder.Fact.convert t f; (acc ++ [f], t)) (([] : List Fact), baseSymbols)
  let (rules, symbols) := b.rules.foldl (fun (acc, t) r =>
    let (r, t) := Builder.Rule.convert t r; (acc ++ [r], t)) (([] : List Rule), symbols)
  let (checks, symbols) := b.checks.foldl (fun (acc, t) c =>
    let (c, t) := Builder.Check.convert t c; (acc ++ [c], t)) (([] : List Check), symbols)
  let (scopes, symbols) := b.scopes.foldl (fun (acc, t) s =>
    let (s, t) := Builder.Scope.convert t s; (acc ++ [s], t)) (([] : List Datalog.Scope), symbols)
  let newSymbols := symbols.symbols.extract symbolStart symbols.symbols.size
  let newKeys := symbols.publicKeys.extract keyStart symbols.publicKeys.size
  { symbols := { symbols := newSymbols, publicKeys := newKeys },
    facts, rules, checks,
    context := b.context,
    version := (getSchemaVersion facts rules checks scopes).version,
    externalKey := none,
    publicKeys := newKeys,
    scopes }

end BlockBuilder

/-- Which signature payload format a new block must use.

Version 1 is required whenever the block could otherwise be replayed or
misread: third-party blocks, blocks using datalog v3.3, and blocks signed with
anything other than Ed25519.  Otherwise a token keeps the format its existing
blocks already use. -/
def blockSignatureVersion (signingAlgorithm nextAlgorithm : Algorithm)
    (hasExternalSignature : Bool) (blockVersion : Option Nat)
    (previousVersions : List Nat) : Nat :=
  if hasExternalSignature then thirdPartySignatureVersion
  else if (blockVersion.getD 0) ≥ datalog33 then 1
  else if signingAlgorithm != .ed25519 || nextAlgorithm != .ed25519 then 1
  else previousVersions.foldl Nat.max 0

namespace Biscuit

/-- Rebuild the decoded view of a container after its blocks changed. -/
def ofContainer (container : Proto.Biscuit) : Except TokenError Biscuit := do
  let blocks ← liftM (((signedBlocks container).mapM fun b =>
    decodeBlock b.block (b.externalSignature.map (·.publicKey))).mapError TokenError.format)
  let symbols ← liftM (buildSymbols blocks |>.mapError TokenError.format)
  pure { container, rootKeyId := container.rootKeyId, symbols, blocks }

/-- Mint a token.

`nextKey` is the ephemeral key pair whose secret travels with the token so that
it can be attenuated; it should be generated at random and then forgotten. -/
def create (root : PrivateKey) (nextKey : PrivateKey) (authority : BlockBuilder)
    (rootKeyId : Option Nat := none) : Except TokenError Biscuit := do
  let block := authority.build {}
  let data := encodeBlock block
  let nextPublic ← liftM ((nextKey.publicKey).mapError TokenError.format)
  let version := blockSignatureVersion root.algorithm nextKey.algorithm false
    (some block.version) []
  let payload :=
    if version == 0 then blockSignaturePayloadV0 data nextPublic none
    else authorityBlockSignaturePayloadV1 data nextPublic version
  let signature ← liftM ((root.sign payload).mapError TokenError.format)
  ofContainer
    { rootKeyId,
      authority := { block := data, nextKey := nextPublic, signature, version },
      blocks := [],
      proof := .secret nextKey.key }

/-- The secret the token carries, which is what allows appending one more
block. -/
def proofKey (b : Biscuit) : Except TokenError PrivateKey := do
  match b.container.proof with
  | .seal _ => throw .appendOnSealed
  | .secret secret =>
    let lastKey := (signedBlocks b.container).getLast!.nextKey
    liftM ((PrivateKey.ofBytes lastKey.algorithm secret).mapError TokenError.format)

/-- The last signature of the chain, which the next block's signature covers. -/
def lastSignature (b : Biscuit) : Bytes := (signedBlocks b.container).getLast!.signature

/-- Append an already serialized block, optionally carrying a third party's
signature. -/
def appendSerialized (b : Biscuit) (nextKey : PrivateKey) (data : Bytes)
    (externalSignature : Option ExternalSignature) (blockVersion : Option Nat) :
    Except TokenError Biscuit := do
  let signingKey ← b.proofKey
  let nextPublic ← liftM ((nextKey.publicKey).mapError TokenError.format)
  let previousVersions := (signedBlocks b.container).map (·.version)
  let version := blockSignatureVersion signingKey.algorithm nextKey.algorithm
    externalSignature.isSome blockVersion previousVersions
  let payload :=
    if version == 0 then blockSignaturePayloadV0 data nextPublic externalSignature
    else blockSignaturePayloadV1 data nextPublic externalSignature b.lastSignature version
  let signature ← liftM ((signingKey.sign payload).mapError TokenError.format)
  ofContainer { b.container with
    blocks := b.container.blocks ++
      [{ block := data, nextKey := nextPublic, signature, externalSignature, version }],
    proof := .secret nextKey.key }

/-- Attenuate the token by appending a block.

The new block can only restrict what the token allows: its checks are added to
those already there, and its rules can only see the facts its scope trusts. -/
def append (b : Biscuit) (nextKey : PrivateKey) (blockBuilder : BlockBuilder) :
    Except TokenError Biscuit := do
  let block := blockBuilder.build b.symbols
  if !b.symbols.isDisjoint block.symbols then
    throw (.format .symbolTableOverlap)
  b.appendSerialized nextKey (encodeBlock block) none (some block.version)

/-- Seal the token, so that no further block can be appended.

The proof stops being a usable secret and becomes a signature over the last
block, which nobody can extend. -/
def sealToken (b : Biscuit) : Except TokenError Biscuit := do
  let signingKey ← b.proofKey
  let last := (signedBlocks b.container).getLast!
  let signature ← liftM ((signingKey.sign (sealSignaturePayloadV0 last)).mapError
    TokenError.format)
  pure { b with container := { b.container with proof := .seal signature } }

/-! ## Third-party blocks

A third party can vouch for a block without ever seeing the token.  It is given
only the previous signature, which is enough to bind its block to that one token
and nothing else. -/

/-- The context a third party needs in order to sign a block for this token. -/
def thirdPartyRequest (b : Biscuit) : ThirdPartyBlockRequest := ⟨b.lastSignature⟩

/-- Sign a block as a third party, in response to a request.

Third-party blocks start from the default symbol table, since the signer does
not have the token's. -/
def signThirdPartyBlock (key : PrivateKey) (request : ThirdPartyBlockRequest)
    (blockBuilder : BlockBuilder) : Except TokenError ThirdPartyBlockContents := do
  let block := blockBuilder.build {}
  let block := { block with version := Nat.max datalog32 block.version }
  let payload := encodeBlock block
  let signature ← liftM ((key.sign (externalSignaturePayloadV1 payload
    request.previousSignature thirdPartySignatureVersion)).mapError TokenError.format)
  let publicKey ← liftM ((key.publicKey).mapError TokenError.format)
  pure ⟨payload, ⟨signature, publicKey⟩⟩

/-- Append a block a third party signed. -/
def appendThirdParty (b : Biscuit) (nextKey : PrivateKey)
    (contents : ThirdPartyBlockContents) : Except TokenError Biscuit :=
  b.appendSerialized nextKey contents.payload (some contents.externalSignature) none

end Biscuit

end Token
end LeanBiscuit
