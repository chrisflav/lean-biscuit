import Lean
import LeanBiscuit

/-!
# The specification's sample tokens

Runs every token in `samples/` through the library and compares the outcome with
the expected result recorded by the specification: the authorization decision,
the revocation identifiers, and the full contents of the datalog world.

The expected values come from the reference implementation, so this is a
conformance test rather than a regression test: it checks that this
implementation agrees with the specification down to the rendering of every
fact, rule and check.
-/

open Lean LeanBiscuit LeanBiscuit.Token LeanBiscuit.Datalog

namespace LeanBiscuit.Tests

/-! ## Rendering results the way the specification records them

The expected values are the JSON serialization of the reference
implementation's Rust types, so the encoding below follows serde's external
tagging: a unit variant is a string, a single-field variant an object with one
key, a multi-field variant an object holding an array or a nested object. -/

/-- A `usize` as JSON. -/
def jnat (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

/-- Encode a signature failure. -/
def signatureErrorJson : SignatureError → Json
  | .invalidFormat => Json.str "InvalidFormat"
  | .invalidSignature m => Json.mkObj [("InvalidSignature", Json.str m)]
  | .invalidSignatureGeneration m => Json.mkObj [("InvalidSignatureGeneration", Json.str m)]

/-- Encode a format failure. -/
def formatErrorJson : FormatError → Json
  | .signature e => Json.mkObj [("Signature", signatureErrorJson e)]
  | .sealedSignature => Json.str "SealedSignature"
  | .emptyKeys => Json.str "EmptyKeys"
  | .unknownPublicKey => Json.str "UnknownPublicKey"
  | .deserializationError m => Json.mkObj [("DeserializationError", Json.str m)]
  | .serializationError m => Json.mkObj [("SerializationError", Json.str m)]
  | .blockDeserializationError m => Json.mkObj [("BlockDeserializationError", Json.str m)]
  | .blockSerializationError m => Json.mkObj [("BlockSerializationError", Json.str m)]
  | .version maximum minimum actual =>
    Json.mkObj [("Version", Json.mkObj
      [("maximum", jnat maximum), ("minimum", jnat minimum), ("actual", jnat actual)])]
  | .invalidKeySize n => Json.mkObj [("InvalidKeySize", jnat n)]
  | .invalidSignatureSize n => Json.mkObj [("InvalidSignatureSize", jnat n)]
  | .invalidKey m => Json.mkObj [("InvalidKey", Json.str m)]
  | .signatureDeserializationError m =>
    Json.mkObj [("SignatureDeserializationError", Json.str m)]
  | .blockSignatureDeserializationError m =>
    Json.mkObj [("BlockSignatureDeserializationError", Json.str m)]
  | .invalidBlockId n => Json.mkObj [("InvalidBlockId", jnat n)]
  | .existingPublicKey m => Json.mkObj [("ExistingPublicKey", Json.str m)]
  | .symbolTableOverlap => Json.str "SymbolTableOverlap"
  | .publicKeyTableOverlap => Json.str "PublicKeyTableOverlap"
  | .unknownExternalKey => Json.str "UnknownExternalKey"
  | .unknownSymbol i => Json.mkObj [("UnknownSymbol", jnat i)]

/-- Encode a failed check. -/
def failedCheckJson : FailedCheck → Json
  | .block blockId checkId rule =>
    Json.mkObj [("Block", Json.mkObj
      [("block_id", jnat blockId), ("check_id", jnat checkId), ("rule", Json.str rule)])]
  | .authorizer checkId rule =>
    Json.mkObj [("Authorizer", Json.mkObj
      [("check_id", jnat checkId), ("rule", Json.str rule)])]

/-- Encode the policy that decided the authorization. -/
def matchedPolicyJson : MatchedPolicy → Json
  | .allow i => Json.mkObj [("Allow", jnat i)]
  | .deny i => Json.mkObj [("Deny", jnat i)]

/-- Encode an authorization failure. -/
def logicErrorJson : LogicError → Json
  | .invalidBlockRule blockId rule =>
    Json.mkObj [("InvalidBlockRule", Json.arr #[jnat blockId, Json.str rule])]
  | .unauthorized policy checks =>
    Json.mkObj [("Unauthorized", Json.mkObj
      [("policy", matchedPolicyJson policy),
       ("checks", Json.arr (checks.map failedCheckJson).toArray)])]
  | .authorizerNotEmpty => Json.str "AuthorizerNotEmpty"
  | .noMatchingPolicy checks =>
    Json.mkObj [("NoMatchingPolicy", Json.mkObj
      [("checks", Json.arr (checks.map failedCheckJson).toArray)])]

/-- Encode an expression failure. -/
def expressionErrorJson : ExpressionError → Json
  | .unknownSymbol i => Json.mkObj [("UnknownSymbol", jnat i)]
  | .unknownVariable i => Json.mkObj [("UnknownVariable", jnat i)]
  | .invalidType => Json.str "InvalidType"
  | .overflow => Json.str "Overflow"
  | .divideByZero => Json.str "DivideByZero"
  | .invalidStack => Json.str "InvalidStack"
  | .shadowedVariable => Json.str "ShadowedVariable"
  | .undefinedExtern n => Json.mkObj [("UndefinedExtern", Json.str n)]
  | .externEvalError n m =>
    Json.mkObj [("ExternEvalError", Json.arr #[Json.str n, Json.str m])]

/-- Encode a runtime limit failure. -/
def runLimitErrorJson : RunLimitError → Json
  | .tooManyFacts => Json.str "TooManyFacts"
  | .tooManyIterations => Json.str "TooManyIterations"
  | .timeout => Json.str "Timeout"
  | .unexpectedQueryResult a b =>
    Json.mkObj [("UnexpectedQueryResult", Json.arr #[jnat a, jnat b])]

/-- Encode any failure. -/
def tokenErrorJson : TokenError → Json
  | .internalError => Json.str "InternalError"
  | .format e => Json.mkObj [("Format", formatErrorJson e)]
  | .appendOnSealed => Json.str "AppendOnSealed"
  | .alreadySealed => Json.str "AlreadySealed"
  | .failedLogic e => Json.mkObj [("FailedLogic", logicErrorJson e)]
  | .language m => Json.mkObj [("Language", Json.str m)]
  | .runLimit e => Json.mkObj [("RunLimit", runLimitErrorJson e)]
  | .conversionError m => Json.mkObj [("ConversionError", Json.str m)]
  | .base64 m => Json.mkObj [("Base64", Json.str m)]
  | .execution e => Json.mkObj [("Execution", expressionErrorJson e)]

/-- Encode an authorization outcome. -/
def resultJson : Except TokenError Nat → Json
  | .ok i => Json.mkObj [("Ok", jnat i)]
  | .error e => Json.mkObj [("Err", tokenErrorJson e)]

/-- Encode a world snapshot the way the specification records it. -/
def worldJson (w : Authorizer.WorldDump) : Json :=
  let originJson : Option Nat → Json
    | none => Json.null
    | some i => jnat i
  -- the reference implementation writes the authorizer's block id, `usize::MAX`,
  -- for the rules and checks it contributed
  let ruleOriginJson : Option Nat → Json
    | none => jnat authorizerBlockId
    | some i => jnat i
  Json.mkObj [
    ("facts", Json.arr (w.facts.map fun (origin, facts) =>
      Json.mkObj [("origin", Json.arr (origin.map originJson).toArray),
                  ("facts", Json.arr (facts.map Json.str).toArray)]).toArray),
    ("rules", Json.arr (w.rules.map fun (origin, rules) =>
      Json.mkObj [("origin", ruleOriginJson origin),
                  ("rules", Json.arr (rules.map Json.str).toArray)]).toArray),
    ("checks", Json.arr (w.checks.map fun (origin, checks) =>
      Json.mkObj [("origin", ruleOriginJson origin),
                  ("checks", Json.arr (checks.map Json.str).toArray)]).toArray),
    ("policies", Json.arr (w.policies.map Json.str).toArray)]

/-! ## The host function the ffi sample expects -/

/-- The `test` external function used by the ffi sample: the identity in its
unary form, and a comparison of two strings in its binary form. -/
def testExtern : ExternFunc := fun left right =>
  match left, right with
  | t, none => .ok t
  | .str a, some (.str b) => .ok (.str (if a == b then "equal strings" else "different strings"))
  | _, _ => .error "unsupported operands"

/-- The external functions the samples are authorized with. -/
def externs : Externs := [("test", testExtern)]

/-! ## Running the samples -/

/-- The outcome of one validation of one sample. -/
structure Outcome where
  /-- The authorization decision. -/
  result : Except TokenError Nat
  /-- The revocation identifiers, hex encoded. -/
  revocationIds : List String
  /-- The world, when the authorizer could be built. -/
  world : Option Authorizer.WorldDump

/-- Authorize one sample token with one authorizer source. -/
def runValidation (data : Bytes) (root : PublicKey) (code : String) : Outcome :=
  match Biscuit.ofBytes data root with
  | .error e => { result := .error e, revocationIds := [], world := none }
  | .ok token =>
    let revocationIds := token.revocationIdentifiers.map Bytes.toHex
    match AuthorizerBuilder.code { externs } code with
    | .error e => { result := .error e, revocationIds, world := none }
    | .ok builder =>
      match Authorizer.build builder token with
      | .error e => { result := .error e, revocationIds, world := none }
      | .ok authorizer =>
        let (result, authorizer) := Authorizer.authorizeWithState authorizer
        { result, revocationIds, world := some (Authorizer.dumpWorld authorizer) }

/-- Look up a field of a JSON object. -/
def field (j : Json) (name : String) : Json := (j.getObjVal? name).toOption.getD Json.null

/-- Compare a produced value with the expected one, reporting a readable
difference. -/
def check (label : String) (actual expected : Json) : List String :=
  if actual.compress == expected.compress then []
  else [s!"  {label}:\n    expected: {expected.compress}\n    actual:   {actual.compress}"]

/-- Run every validation of every sample, returning the failures. -/
def run (samplesDir : System.FilePath) : IO (Nat × List String) := do
  let text ← IO.FS.readFile (samplesDir / "samples.json")
  let json ← IO.ofExcept (Json.parse text)
  let rootHex ← IO.ofExcept ((field json "root_public_key").getStr?)
  let some rootBytes := Bytes.ofHex? rootHex
    | throw (IO.userError "the sample root public key is not valid hexadecimal")
  let root : PublicKey := ⟨.ed25519, rootBytes⟩
  let testcases ← IO.ofExcept ((field json "testcases").getArr?)
  let mut failures : List String := []
  let mut count := 0
  for testcase in testcases do
    let filename ← IO.ofExcept ((field testcase "filename").getStr?)
    let title ← IO.ofExcept ((field testcase "title").getStr?)
    let data ← IO.FS.readBinFile (samplesDir / filename)
    let validations ← IO.ofExcept ((field testcase "validations").getObj?)
    for (name, validation) in validations.toArray do
      count := count + 1
      let code ← IO.ofExcept ((field validation "authorizer_code").getStr?)
      let outcome := runValidation data root code
      let label := if name.isEmpty then filename else s!"{filename} [{name}]"
      let mut diffs : List String := []
      diffs := diffs ++ check "result" (resultJson outcome.result) (field validation "result")
      diffs := diffs ++ check "revocation_ids"
        (Json.arr (outcome.revocationIds.map Json.str).toArray)
        (field validation "revocation_ids")
      diffs := diffs ++ check "world"
        (match outcome.world with
         | none => Json.null
         | some w => worldJson w)
        (field validation "world")
      if !diffs.isEmpty then
        failures := failures ++ [s!"{label} ({title})\n" ++ String.intercalate "\n" diffs]
  pure (count, failures)

end LeanBiscuit.Tests
