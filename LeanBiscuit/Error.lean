/-!
# Error types

The error hierarchy mirrors the one described by the specification and used by
the reference implementation, so that the failure of an authorization can be
reported precisely: which layer rejected the token (wire format, signature,
datalog execution, or the authorization decision itself) and why.
-/

namespace LeanBiscuit

/-- Failures of a cryptographic signature check. -/
inductive SignatureError where
  /-- The signature elements could not be parsed. -/
  | invalidFormat
  /-- The signature did not match the payload. -/
  | invalidSignature (message : String)
  /-- A signature could not be produced. -/
  | invalidSignatureGeneration (message : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Failures related to the serialization format or the signature chain. -/
inductive FormatError where
  /-- A block signature did not verify. -/
  | signature (error : SignatureError)
  /-- The final signature of a sealed token did not verify. -/
  | sealedSignature
  /-- The token carries no intermediate public keys. -/
  | emptyKeys
  /-- The root public key was not recognised. -/
  | unknownPublicKey
  /-- The outer `Biscuit` message could not be decoded. -/
  | deserializationError (message : String)
  /-- The outer `Biscuit` message could not be encoded. -/
  | serializationError (message : String)
  /-- A `Block` message could not be decoded. -/
  | blockDeserializationError (message : String)
  /-- A `Block` message could not be encoded. -/
  | blockSerializationError (message : String)
  /-- The block's datalog version is outside the supported range. -/
  | version (maximum minimum actual : Nat)
  /-- A key had the wrong length. -/
  | invalidKeySize (size : Nat)
  /-- A signature had the wrong length. -/
  | invalidSignatureSize (size : Nat)
  /-- A key was malformed. -/
  | invalidKey (message : String)
  /-- A signature could not be deserialized. -/
  | signatureDeserializationError (message : String)
  /-- A block signature could not be deserialized. -/
  | blockSignatureDeserializationError (message : String)
  /-- A block index was out of range. -/
  | invalidBlockId (id : Nat)
  /-- A public key was already present in a previous block. -/
  | existingPublicKey (message : String)
  /-- Two blocks declare the same symbol. -/
  | symbolTableOverlap
  /-- Two blocks declare the same public key. -/
  | publicKeyTableOverlap
  /-- An external public key was not recognised. -/
  | unknownExternalKey
  /-- A symbol index was not present in the symbol table. -/
  | unknownSymbol (index : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Failures while evaluating a datalog expression. -/
inductive ExpressionError where
  /-- A term referred to an absent symbol. -/
  | unknownSymbol (index : Nat)
  /-- An opcode referred to a variable that is not bound by the rule body. -/
  | unknownVariable (index : Nat)
  /-- An operation was applied to operands of the wrong type. -/
  | invalidType
  /-- An integer operation overflowed. -/
  | overflow
  /-- An integer division by zero. -/
  | divideByZero
  /-- The stack did not hold exactly one value at the end of evaluation. -/
  | invalidStack
  /-- A closure parameter shadows a variable already in scope. -/
  | shadowedVariable
  /-- An external call named a function the host did not provide. -/
  | undefinedExtern (name : String)
  /-- An external call failed. -/
  | externEvalError (name : String) (message : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A check that did not succeed, together with a rendering of its query. -/
inductive FailedCheck where
  /-- A check carried by block `blockId`. -/
  | block (blockId : Nat) (checkId : Nat) (rule : String)
  /-- A check provided by the authorizer. -/
  | authorizer (checkId : Nat) (rule : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The policy that decided the authorization. -/
inductive MatchedPolicy where
  /-- An `allow` policy at the given index matched. -/
  | allow (index : Nat)
  /-- A `deny` policy at the given index matched. -/
  | deny (index : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Failures of the datalog evaluation and of the authorization decision. -/
inductive LogicError where
  /-- A block rule would produce a fact with unbound variables. -/
  | invalidBlockRule (blockId : Nat) (rule : String)
  /-- A policy matched but some checks failed, or a `deny` policy matched. -/
  | unauthorized (policy : MatchedPolicy) (checks : List FailedCheck)
  /-- The authorizer already contains a token. -/
  | authorizerNotEmpty
  /-- No policy matched. -/
  | noMatchingPolicy (checks : List FailedCheck)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The datalog engine hit one of its runtime limits. -/
inductive RunLimitError where
  /-- More facts were generated than the limit allows. -/
  | tooManyFacts
  /-- The fixpoint was not reached within the iteration limit. -/
  | tooManyIterations
  /-- Evaluation took longer than allowed. -/
  | timeout
  /-- A query returned an unexpected number of results. -/
  | unexpectedQueryResult (expected got : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The top level error type. -/
inductive TokenError where
  /-- An invariant of the library was violated. -/
  | internalError
  /-- The token could not be decoded or its signatures did not verify. -/
  | format (error : FormatError)
  /-- A block was appended to a sealed token. -/
  | appendOnSealed
  /-- An already sealed token was sealed again. -/
  | alreadySealed
  /-- Authorization failed. -/
  | failedLogic (error : LogicError)
  /-- Datalog source could not be parsed. -/
  | language (message : String)
  /-- A datalog runtime limit was reached. -/
  | runLimit (error : RunLimitError)
  /-- A term could not be converted to the requested type. -/
  | conversionError (message : String)
  /-- The base64 envelope could not be decoded. -/
  | base64 (message : String)
  /-- A datalog expression failed to evaluate. -/
  | execution (error : ExpressionError)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Datalog execution can fail either by hitting a runtime limit or by failing
to evaluate an expression. -/
inductive ExecutionError where
  /-- A runtime limit was reached. -/
  | runLimit (error : RunLimitError)
  /-- An expression failed to evaluate. -/
  | expression (error : ExpressionError)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace ExecutionError

/-- Lift an execution error into the top level error type, as the reference
implementation's `From<Execution> for Token` does. -/
def toTokenError : ExecutionError → TokenError
  | .runLimit e => .runLimit e
  | .expression e => .execution e

end ExecutionError

/-! ## Human readable messages

The wording follows the reference implementation, extended with the detail each
variant carries so that a failure can be diagnosed from the message alone. -/

namespace SignatureError

/-- Describe a signature failure. -/
def toString : SignatureError → String
  | .invalidFormat => "could not parse the signature elements"
  | .invalidSignature m => s!"the signature did not match: {m}"
  | .invalidSignatureGeneration m => s!"could not sign: {m}"

instance : ToString SignatureError := ⟨toString⟩

end SignatureError

namespace FormatError

/-- Describe a format failure. -/
def toString : FormatError → String
  | .signature e => s!"failed verifying the signature: {e}"
  | .sealedSignature => "failed verifying the signature of a sealed token"
  | .emptyKeys => "the token does not provide intermediate public keys"
  | .unknownPublicKey => "the root public key was not recognized"
  | .deserializationError m => s!"could not deserialize the wrapper object: {m}"
  | .serializationError m => s!"could not serialize the wrapper object: {m}"
  | .blockDeserializationError m => s!"could not deserialize the block: {m}"
  | .blockSerializationError m => s!"could not serialize the block: {m}"
  | .version maximum minimum actual =>
    s!"block format version {actual} is outside the supported range {minimum}..{maximum}"
  | .invalidKeySize n => s!"invalid key size: {n}"
  | .invalidSignatureSize n => s!"invalid signature size: {n}"
  | .invalidKey m => s!"invalid key: {m}"
  | .signatureDeserializationError m => s!"could not deserialize signature: {m}"
  | .blockSignatureDeserializationError m => s!"could not deserialize the block signature: {m}"
  | .invalidBlockId n => s!"invalid block id: {n}"
  | .existingPublicKey m => s!"the public key is already present in previous blocks: {m}"
  | .symbolTableOverlap => "multiple blocks declare the same symbols"
  | .publicKeyTableOverlap => "multiple blocks declare the same public keys"
  | .unknownExternalKey => "the external public key was not recognized"
  | .unknownSymbol i => s!"the symbol id {i} was not in the table"

instance : ToString FormatError := ⟨toString⟩

end FormatError

namespace ExpressionError

/-- Describe an expression failure. -/
def toString : ExpressionError → String
  | .unknownSymbol i => s!"unknown symbol {i}"
  | .unknownVariable i => s!"unknown variable {i}"
  | .invalidType => "invalid type"
  | .overflow => "overflow"
  | .divideByZero => "division by zero"
  | .invalidStack => "wrong number of elements on stack"
  | .shadowedVariable => "shadowed variable"
  | .undefinedExtern n => s!"undefined extern func: {n}"
  | .externEvalError n m => s!"error while evaluating extern func {n}: {m}"

instance : ToString ExpressionError := ⟨toString⟩

end ExpressionError

namespace FailedCheck

/-- Describe a failed check. -/
def toString : FailedCheck → String
  | .block blockId checkId rule => s!"check n°{checkId} in block n°{blockId}: {rule}"
  | .authorizer checkId rule => s!"check n°{checkId} in authorizer: {rule}"

instance : ToString FailedCheck := ⟨toString⟩

end FailedCheck

namespace MatchedPolicy

/-- Describe the policy that decided the authorization. -/
def toString : MatchedPolicy → String
  | .allow i => s!"an allow policy matched (policy index: {i})"
  | .deny i => s!"a deny policy matched (policy index: {i})"

instance : ToString MatchedPolicy := ⟨toString⟩

end MatchedPolicy

namespace LogicError

/-- Describe an authorization failure. -/
def toString : LogicError → String
  | .invalidBlockRule _ rule =>
    s!"a rule provided by a block is producing a fact with unbound variables: {rule}"
  | .unauthorized policy checks =>
    s!"{policy}, and the following checks failed: "
      ++ String.intercalate ", " (checks.map FailedCheck.toString)
  | .authorizerNotEmpty => "the authorizer already contains a token"
  | .noMatchingPolicy checks =>
    "no matching policy was found, and the following checks failed: "
      ++ String.intercalate ", " (checks.map FailedCheck.toString)

instance : ToString LogicError := ⟨toString⟩

end LogicError

namespace RunLimitError

/-- Describe a runtime limit failure. -/
def toString : RunLimitError → String
  | .tooManyFacts => "too many facts generated"
  | .tooManyIterations => "too many engine iterations"
  | .timeout => "spent too much time verifying"
  | .unexpectedQueryResult expected got =>
    s!"unexpected query results, expected {expected} got {got}"

instance : ToString RunLimitError := ⟨toString⟩

end RunLimitError

namespace TokenError

/-- Describe any failure. -/
def toString : TokenError → String
  | .internalError => "internal error"
  | .format e => s!"error deserializing or verifying the token: {e}"
  | .appendOnSealed => "tried to append a block to a sealed token"
  | .alreadySealed => "tried to seal an already sealed token"
  | .failedLogic e => s!"authorization failed: {e}"
  | .language m => s!"error parsing datalog: {m}"
  | .runLimit e => s!"reached datalog execution limits: {e}"
  | .conversionError m => s!"cannot convert from term: {m}"
  | .base64 m => s!"cannot decode base64 token: {m}"
  | .execution e => s!"datalog execution failure: {e}"

instance : ToString TokenError := ⟨toString⟩

end TokenError

/-- The result of a fallible biscuit operation. -/
abbrev TokenResult (α : Type) := Except TokenError α

end LeanBiscuit
