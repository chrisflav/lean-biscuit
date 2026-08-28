import LeanBiscuit.Proto.Schema
import LeanBiscuit.Datalog.World

/-!
# Blocks

A block carries the datalog a token contributes: facts, rules, checks, its own
symbols and public keys, and the trust annotation that applies to all of its
rules.

Each block records the datalog version it was written for.  An implementation
must refuse a block whose version it does not know, in either direction: a newer
one might use constructs it would silently misinterpret, and an older one might
be interpreted with the wrong semantics.  A block must also actually stay within
the features its declared version allows, which is what `checkCompatibility`
enforces.
-/

namespace LeanBiscuit
namespace Token

open Datalog Proto Proto.Wire

/-- The lowest datalog version this implementation understands (biscuit v3.0). -/
def minSchemaVersion : Nat := 3

/-- The version that introduced scopes, `check all`, bitwise operators and
`!==` (biscuit v3.1). -/
def datalog31 : Nat := 4

/-- The version that introduced third-party blocks (biscuit v3.2). -/
def datalog32 : Nat := 5

/-- The version that introduced null, arrays, maps, closures, heterogeneous
equality and external calls (biscuit v3.3). -/
def datalog33 : Nat := 6

/-- The highest datalog version this implementation understands. -/
def maxSchemaVersion : Nat := datalog33

/-- The datalog contributed by one block. -/
structure Block where
  /-- The symbols and public keys this block introduces. -/
  symbols : SymbolTable := {}
  /-- The facts it states. -/
  facts : List Fact := []
  /-- The rules it defines. -/
  rules : List Rule := []
  /-- The checks it imposes. -/
  checks : List Check := []
  /-- Free-form context, not interpreted. -/
  context : Option String := none
  /-- The datalog version this block was written for. -/
  version : Nat := minSchemaVersion
  /-- The third party that signed this block, if any. -/
  externalKey : Option PublicKey := none
  /-- The public keys this block introduces, in order. -/
  publicKeys : Array PublicKey := #[]
  /-- The trust annotation that applies to the whole block. -/
  scopes : List Scope := []
  deriving Repr, Inhabited

namespace Decode

/-- Report a malformed block. -/
def fail (message : String) : Except FormatError α :=
  throw (.blockDeserializationError s!"deserialization error: {message}")

/-- The constructor tag of a `Term` message, used to check that a set is
homogeneous. -/
def termKind (f : Fields) : Option Nat :=
  if (last? f 1).isSome then some 1
  else if (last? f 2).isSome then some 2
  else if (last? f 3).isSome then some 3
  else if (last? f 4).isSome then some 4
  else if (last? f 5).isSome then some 5
  else if (last? f 6).isSome then some 6
  else if (last? f 7).isSome then some 7
  else if (last? f 8).isSome then some 8
  else if (last? f 9).isSome then some 9
  else if (last? f 10).isSome then some 10
  else none

/-! Decoding descends into nested messages, and the size of the enclosing byte
string bounds how deep that can go: every level of nesting costs at least a tag
and a length byte.  `fuel` carries that bound, so the decoders are total. -/

mutual

/-- Decode a `Term` message. -/
def decodeTerm (fuel : Nat) (f : Fields) : Except FormatError Term := do
  match fuel with
  | 0 => fail "term is nested too deeply"
  | fuel + 1 =>
    match termKind f with
    | none => fail "term content enum is empty"
    | some 1 => pure (.variable ((uint? f 1).getD 0))
    | some 2 => pure (.integer ((int? f 2).getD 0))
    | some 3 => pure (.str ((uint? f 3).getD 0))
    | some 4 => pure (.date ((uint? f 4).getD 0))
    | some 5 => pure (.bytes ((bytes? f 5).getD Bytes.empty))
    | some 6 => pure (.bool ((bool? f 6).getD false))
    | some 7 => do
      let .ok (some setFields) := message? f 7 | fail "could not decode a set"
      let .ok elementFields := allMessages setFields 1 | fail "could not decode a set element"
      -- a set must be homogeneous, and may contain neither variables nor sets
      let mut kind : Option Nat := none
      for ef in elementFields do
        match termKind ef with
        | none => fail "term content enum is empty"
        | some 1 => fail "sets cannot contain variables"
        | some 7 => fail "sets cannot contain other sets"
        | some k =>
          match kind with
          | some k' => if k' != k then fail "sets elements must have the same type"
          | none => kind := some k
      pure (.set (mkSet (← decodeTermList fuel elementFields)))
    | some 8 => pure .null
    | some 9 => do
      let .ok (some arrayFields) := message? f 9 | fail "could not decode an array"
      let .ok elementFields := allMessages arrayFields 1 | fail "could not decode an array element"
      pure (.array (← decodeTermList fuel elementFields))
    | some 10 => do
      let .ok (some mapFields) := message? f 10 | fail "could not decode a map"
      let .ok entryFields := allMessages mapFields 1 | fail "could not decode a map entry"
      pure (.map (mkMap (← decodeEntryList fuel entryFields)))
    | some _ => fail "term content enum is empty"
termination_by (fuel, 0, 0)

/-- Decode each `Term` of a list. -/
def decodeTermList (fuel : Nat) : List Fields → Except FormatError (List Term)
  | [] => pure []
  | f :: rest => do pure ((← decodeTerm fuel f) :: (← decodeTermList fuel rest))
termination_by l => (fuel, 1, l.length)

/-- Decode each `MapEntry` of a list. -/
def decodeEntryList (fuel : Nat) : List Fields → Except FormatError (List (MapKey × Term))
  | [] => pure []
  | ef :: rest => do
    let .ok (some keyFields) := message? ef 1 | fail "could not decode a map key"
    let key ←
      if let some i := int? keyFields 1 then pure (MapKey.integer i)
      else if let some s := uint? keyFields 2 then pure (MapKey.str s)
      else fail "map key content enum is empty"
    let .ok (some valueFields) := message? ef 2 | fail "could not decode a map value"
    pure ((key, ← decodeTerm fuel valueFields) :: (← decodeEntryList fuel rest))
termination_by l => (fuel, 1, l.length)

end

/-- Decode a `Predicate` message. -/
def decodePredicate (fuel : Nat) (f : Fields) : Except FormatError Predicate := do
  let some name := uint? f 1 | fail "missing predicate name"
  let .ok termFields := allMessages f 2 | fail "could not decode a predicate term"
  pure ⟨name, ← decodeTermList fuel termFields⟩

/-- Decode a `Scope` message. -/
def decodeScope (f : Fields) : Except FormatError Scope := do
  if let some t := uint? f 1 then
    if t == 0 then pure .authority
    else if t == 1 then pure .previous
    else fail s!"unexpected value `{t}` for scope type"
  else if let some i := int? f 2 then
    pure (.publicKey (if i < 0 then (i + 2 ^ 64).toNat else i.toNat))
  else fail "expected `content` field in Scope"

mutual

/-- Decode an `Op` message. -/
def decodeOp (fuel : Nat) (f : Fields) : Except FormatError Op := do
  match fuel with
  | 0 => fail "expression is nested too deeply"
  | fuel + 1 =>
    if let .ok (some valueFields) := message? f 1 then
      pure (.value (← decodeTerm fuel valueFields))
    else if let .ok (some unaryFields) := message? f 2 then
      let some kind := uint? unaryFields 1 | fail "unary operation is empty"
      let name := uint? unaryFields 2
      match kind, name with
      | 0, none => pure (.unary .negate)
      | 1, none => pure (.unary .parens)
      | 2, none => pure (.unary .length)
      | 3, none => pure (.unary .typeOf)
      | 4, some n => pure (.unary (.ffi n))
      | 4, none => fail "missing ffi name"
      | _, some _ => fail "ffi name set on a regular unary operation"
      | _, none => fail "unary operation is empty"
    else if let .ok (some binaryFields) := message? f 3 then
      let some kind := uint? binaryFields 1 | fail "binary operation is empty"
      let name := uint? binaryFields 2
      match name with
      | some n => if kind == 28 then pure (.binary (.ffi n))
                  else fail "ffi name set on a regular binary operation"
      | none =>
        match kind with
        | 0 => pure (.binary .lessThan)
        | 1 => pure (.binary .greaterThan)
        | 2 => pure (.binary .lessOrEqual)
        | 3 => pure (.binary .greaterOrEqual)
        | 4 => pure (.binary .equal)
        | 5 => pure (.binary .contains)
        | 6 => pure (.binary .startsWith)
        | 7 => pure (.binary .endsWith)
        | 8 => pure (.binary .regex)
        | 9 => pure (.binary .add)
        | 10 => pure (.binary .sub)
        | 11 => pure (.binary .mul)
        | 12 => pure (.binary .div)
        | 13 => pure (.binary .and)
        | 14 => pure (.binary .or)
        | 15 => pure (.binary .intersection)
        | 16 => pure (.binary .union)
        | 17 => pure (.binary .bitwiseAnd)
        | 18 => pure (.binary .bitwiseOr)
        | 19 => pure (.binary .bitwiseXor)
        | 20 => pure (.binary .notEqual)
        | 21 => pure (.binary .heterogeneousEqual)
        | 22 => pure (.binary .heterogeneousNotEqual)
        | 23 => pure (.binary .lazyAnd)
        | 24 => pure (.binary .lazyOr)
        | 25 => pure (.binary .all)
        | 26 => pure (.binary .any)
        | 27 => pure (.binary .get)
        | 28 => fail "missing ffi name"
        | 29 => pure (.binary .tryOr)
        | _ => fail "binary operation is empty"
    else if let .ok (some closureFields) := message? f 4 then
      -- `repeated uint32` is unpacked in proto2, but accept the packed form too
      let params := (all closureFields 1).flatMap fun
        | .varint v => [v]
        | .bytes b =>
          let rec unpack (i : Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
            match fuel with
            | 0 => acc
            | fuel + 1 =>
              match readVarint b i with
              | .ok (v, j) => if j > i then unpack j (acc ++ [v]) fuel else acc
              | .error _ => acc
          unpack 0 [] b.size
        | _ => []
      let .ok opFields := allMessages closureFields 2 | fail "could not decode a closure opcode"
      pure (.closure params (← decodeOpList fuel opFields))
    else fail "operation is empty"
termination_by (fuel, 0)

/-- Decode each `Op` of a list. -/
def decodeOpList (fuel : Nat) : List Fields → Except FormatError (List Op)
  | [] => pure []
  | f :: rest => do pure ((← decodeOp fuel f) :: (← decodeOpList fuel rest))
termination_by l => (fuel, l.length)

end

/-- Decode an `Expression` message. -/
def decodeExpression (fuel : Nat) (f : Fields) : Except FormatError Expression := do
  let .ok opFields := allMessages f 1 | fail "could not decode an opcode"
  pure ⟨← decodeOpList fuel opFields⟩

/-- Decode a `Rule` message.  Scopes are only allowed from datalog v3.1 on. -/
def decodeRule (fuel : Nat) (f : Fields) (version : Nat) : Except FormatError Rule := do
  let .ok (some headFields) := message? f 1 | fail "missing rule head"
  let head ← decodePredicate fuel headFields
  let .ok bodyFields := allMessages f 2 | fail "could not decode a rule body predicate"
  let body ← bodyFields.mapM (decodePredicate fuel)
  let .ok exprFields := allMessages f 3 | fail "could not decode a rule expression"
  let expressions ← exprFields.mapM (decodeExpression fuel)
  let .ok scopeFields := allMessages f 4 | fail "could not decode a rule scope"
  if version < datalog31 && !scopeFields.isEmpty then
    fail "scopes are only supported in datalog v3.1+"
  let scopes ← scopeFields.mapM decodeScope
  pure { head, body, expressions, scopes }

/-- Decode a `Check` message. -/
def decodeCheck (fuel : Nat) (f : Fields) (version : Nat) : Except FormatError Check := do
  let .ok queryFields := allMessages f 1 | fail "could not decode a check query"
  let queries ← queryFields.mapM (decodeRule fuel · version)
  let kind ←
    match uint? f 2 with
    | none | some 0 => pure CheckKind.one
    | some 1 => pure CheckKind.all
    | some 2 => pure CheckKind.reject
    | some _ => fail "invalid check kind"
  pure { queries, kind }

/-- Decode a `Fact` message. -/
def decodeFact (fuel : Nat) (f : Fields) : Except FormatError Fact := do
  let .ok (some predFields) := message? f 1 | fail "missing fact predicate"
  pure ⟨← decodePredicate fuel predFields⟩

end Decode

/-! ## Version compatibility -/

/-- Does any opcode need datalog v3.1? -/
def containsV31Op (expressions : List Expression) : Bool :=
  expressions.any fun e => e.ops.any fun
    | .binary .bitwiseAnd | .binary .bitwiseOr | .binary .bitwiseXor | .binary .notEqual => true
    | _ => false

/-- Does a term need datalog v3.3?  Null does, directly or inside a set. -/
def containsV33Term : Term → Bool
  | .null => true
  | .set s => s.any fun | .null => true | _ => false
  | _ => false

/-- Does a predicate carry a term that needs datalog v3.3? -/
def containsV33Predicate (p : Predicate) : Bool := p.terms.any containsV33Term

/-- Does any opcode need datalog v3.3? -/
def containsV33Op (expressions : List Expression) : Bool :=
  expressions.any fun e => e.ops.any fun
    | .value t => containsV33Term t
    | .closure _ _ => true
    | .unary .typeOf | .unary (.ffi _) => true
    | .binary .heterogeneousEqual | .binary .heterogeneousNotEqual
    | .binary .lazyAnd | .binary .lazyOr
    | .binary .all | .binary .any | .binary (.ffi _) => true
    | _ => false

/-- The features a block's contents use, from which its minimum version
follows. -/
structure SchemaVersion where
  /-- Does it use trust annotations? -/
  containsScopes : Bool
  /-- Does it use a v3.1 operator? -/
  containsV31 : Bool
  /-- Does it use `check all`? -/
  containsCheckAll : Bool
  /-- Does it use a v3.3 feature? -/
  containsV33 : Bool
  deriving Repr

/-- Determine which features a block's contents use. -/
def getSchemaVersion (facts : List Fact) (rules : List Rule) (checks : List Check)
    (scopes : List Scope) : SchemaVersion :=
  let containsScopes :=
    !scopes.isEmpty || rules.any (!·.scopes.isEmpty)
      || checks.any fun c => c.queries.any (!·.scopes.isEmpty)
  let containsCheckAll := checks.any (·.kind == .all)
  let containsReject := checks.any (·.kind == .reject)
  let containsV31 :=
    rules.any (fun r => containsV31Op r.expressions)
      || checks.any fun c => c.queries.any fun q => containsV31Op q.expressions
  let containsV33 :=
    containsReject
      || rules.any (fun r =>
          containsV33Predicate r.head || r.body.any containsV33Predicate
            || containsV33Op r.expressions)
      || checks.any (fun c => c.queries.any fun q =>
          q.body.any containsV33Predicate || containsV33Op q.expressions)
      || facts.any fun f => containsV33Predicate f.predicate
  { containsScopes, containsV31, containsCheckAll, containsV33 }

/-- The lowest version that can express these features. -/
def SchemaVersion.version (v : SchemaVersion) : Nat :=
  if v.containsV33 then datalog33
  else if v.containsScopes || v.containsV31 || v.containsCheckAll then datalog31
  else minSchemaVersion

/-- Reject a block that uses features its declared version does not have. -/
def SchemaVersion.checkCompatibility (v : SchemaVersion) (version : Nat) :
    Except FormatError Unit :=
  if version < datalog31 then
    if v.containsScopes then
      throw (.deserializationError "scopes are only supported in datalog v3.1+")
    else if v.containsV31 then
      throw (.deserializationError
        "bitwise operators and != are only supported in datalog v3.1+")
    else if v.containsCheckAll then
      throw (.deserializationError "check all is only supported in datalog v3.1+")
    else pure ()
  else if version < datalog33 && v.containsV33 then
    throw (.deserializationError
      "maps, arrays, null, closures are only supported in datalog v3.3+")
  else pure ()

/-- Decode the serialized datalog of a block.

`externalKey` is the third party key from the enclosing `SignedBlock`, which the
block itself does not carry but whose presence constrains the version. -/
def decodeBlock (data : Bytes) (externalKey : Option PublicKey) : Except FormatError Block := do
  let .ok f := Wire.decode data
    | throw (.blockDeserializationError "error deserializing block")
  let version := (uint? f 3).getD 0
  if version < minSchemaVersion || version > maxSchemaVersion then
    throw (.version maxSchemaVersion minSchemaVersion version)
  -- the size of the block bounds how deeply its messages can nest
  let fuel := data.size + 1
  let .ok factFields := allMessages f 4 | Decode.fail "could not decode a fact"
  let facts ← factFields.mapM (Decode.decodeFact fuel)
  let .ok ruleFields := allMessages f 5 | Decode.fail "could not decode a rule"
  let rules ← ruleFields.mapM (Decode.decodeRule fuel · version)
  let .ok checkFields := allMessages f 6 | Decode.fail "could not decode a check"
  if version < maxSchemaVersion then
    for c in checkFields do
      match uint? c 2 with
      | none => pure ()
      | some k =>
        if version < datalog31 then
          throw (.deserializationError
            "deserialization error: check kinds are only supported on datalog v3.1+ blocks")
        else if version < datalog33 && k == 2 then
          throw (.deserializationError
            "deserialization error: reject if is only supported in datalog v3.3+")
  if version < datalog32 && externalKey.isSome then
    throw (.deserializationError
      "deserialization error: third-party blocks are only supported in datalog v3.2+")
  let checks ← checkFields.mapM (Decode.decodeCheck fuel · version)
  let .ok scopeFields := allMessages f 7 | Decode.fail "could not decode a block scope"
  let scopes ← scopeFields.mapM Decode.decodeScope
  let .ok keyFields := allMessages f 8 | Decode.fail "could not decode a public key"
  let mut publicKeys : SymbolTable := {}
  for kf in keyFields do
    let key ← Proto.Schema.decodePublicKey kf
    let (_, t) ← publicKeys.insertKeyFallible key
    publicKeys := t
  let mut symbols ← SymbolTable.ofStrings (allStrings f 1)
  symbols := { symbols with publicKeys := publicKeys.publicKeys }
  (getSchemaVersion facts rules checks scopes).checkCompatibility version
  pure { symbols, facts, rules, checks, context := string? f 2, version, externalKey,
         publicKeys := publicKeys.publicKeys, scopes }

/-! ## Encoding

Serializing a block is what an implementation does when it creates or attenuates
a token; the resulting bytes are exactly what the block's signature covers, so
the encoding must be stable. -/

namespace Encode

open Datalog

mutual

/-- Encode a `Term` message. -/
def term : Datalog.Term → Bytes
  | .variable i => encodeUint 1 i
  | .integer i => encodeInt 2 i
  | .str i => encodeUint 3 i
  | .date d => encodeUint 4 d
  | .bytes b => encodeBytes 5 b
  | .bool b => encodeBool 6 b
  | .set l => encodeBytes 7 (Bytes.concat (termList l))
  | .null => encodeBytes 8 Bytes.empty
  | .array l => encodeBytes 9 (Bytes.concat (termList l))
  | .map entries => encodeBytes 10 (Bytes.concat (entryList entries))

/-- Encode each element of a set or array. -/
def termList : List Datalog.Term → List Bytes
  | [] => []
  | x :: xs => encodeBytes 1 (term x) :: termList xs

/-- Encode each entry of a map. -/
def entryList : List (Datalog.MapKey × Datalog.Term) → List Bytes
  | [] => []
  | (k, v) :: xs =>
    let key := match k with
      | .integer i => encodeInt 1 i
      | .str s => encodeUint 2 s
    encodeBytes 1 (encodeBytes 1 key ++ encodeBytes 2 (term v)) :: entryList xs

end

/-- Encode a `Predicate` message. -/
def predicate (p : Predicate) : Bytes :=
  encodeUint 1 p.name ++ Bytes.concat (p.terms.map fun t => encodeBytes 2 (term t))

/-- Encode a `Fact` message. -/
def fact (f : Fact) : Bytes := encodeBytes 1 (predicate f.predicate)

/-- Encode a `Scope` message. -/
def scope : Datalog.Scope → Bytes
  | .authority => encodeUint 1 0
  | .previous => encodeUint 1 1
  | .publicKey i => encodeInt 2 (i : Int)

/-- The protobuf tag of a unary opcode. -/
def unaryKind : Datalog.Unary → Nat
  | .negate => 0
  | .parens => 1
  | .length => 2
  | .typeOf => 3
  | .ffi _ => 4

/-- The protobuf tag of a binary opcode. -/
def binaryKind : Datalog.Binary → Nat
  | .lessThan => 0
  | .greaterThan => 1
  | .lessOrEqual => 2
  | .greaterOrEqual => 3
  | .equal => 4
  | .contains => 5
  | .startsWith => 6
  | .endsWith => 7
  | .regex => 8
  | .add => 9
  | .sub => 10
  | .mul => 11
  | .div => 12
  | .and => 13
  | .or => 14
  | .intersection => 15
  | .union => 16
  | .bitwiseAnd => 17
  | .bitwiseOr => 18
  | .bitwiseXor => 19
  | .notEqual => 20
  | .heterogeneousEqual => 21
  | .heterogeneousNotEqual => 22
  | .lazyAnd => 23
  | .lazyOr => 24
  | .all => 25
  | .any => 26
  | .get => 27
  | .ffi _ => 28
  | .tryOr => 29

mutual

/-- Encode an `Op` message. -/
def op : Datalog.Op → Bytes
  | .value t => encodeBytes 1 (term t)
  | .unary u =>
    encodeBytes 2 (encodeUint 1 (unaryKind u) ++
      (match u with | .ffi n => encodeUint 2 n | _ => Bytes.empty))
  | .binary b =>
    encodeBytes 3 (encodeUint 1 (binaryKind b) ++
      (match b with | .ffi n => encodeUint 2 n | _ => Bytes.empty))
  | .closure params ops =>
    encodeBytes 4 (Bytes.concat (params.map (encodeUint 1)) ++ Bytes.concat (opList ops))

/-- Encode each opcode of a sequence. -/
def opList : List Datalog.Op → List Bytes
  | [] => []
  | o :: rest => encodeBytes 2 (op o) :: opList rest

end

/-- Encode an `Expression` message. -/
def expression (e : Expression) : Bytes :=
  Bytes.concat (e.ops.map fun o => encodeBytes 1 (op o))

/-- Encode a `Rule` message. -/
def rule (r : Datalog.Rule) : Bytes :=
  encodeBytes 1 (predicate r.head)
    ++ Bytes.concat (r.body.map fun p => encodeBytes 2 (predicate p))
    ++ Bytes.concat (r.expressions.map fun e => encodeBytes 3 (expression e))
    ++ Bytes.concat (r.scopes.map fun s => encodeBytes 4 (scope s))

/-- Encode a `Check` message. -/
def check (c : Check) : Bytes :=
  Bytes.concat (c.queries.map fun q => encodeBytes 1 (rule q))
    ++ (match c.kind with
        | .one => Bytes.empty
        | .all => encodeUint 2 1
        | .reject => encodeUint 2 2)

end Encode

/-- Serialize a block's datalog.  These are the bytes the block's signature
covers. -/
def encodeBlock (b : Block) : Bytes :=
  Bytes.concat (b.symbols.symbols.toList.map (Wire.encodeString 1))
    ++ (match b.context with
        | none => Bytes.empty
        | some c => Wire.encodeString 2 c)
    ++ Wire.encodeUint 3 b.version
    ++ Bytes.concat (b.facts.map fun f => Wire.encodeBytes 4 (Encode.fact f))
    ++ Bytes.concat (b.rules.map fun r => Wire.encodeBytes 5 (Encode.rule r))
    ++ Bytes.concat (b.checks.map fun c => Wire.encodeBytes 6 (Encode.check c))
    ++ Bytes.concat (b.scopes.map fun s => Wire.encodeBytes 7 (Encode.scope s))
    ++ Bytes.concat (b.publicKeys.toList.map fun k =>
         Wire.encodeBytes 8 (Proto.Schema.encodePublicKey k))

end Token
end LeanBiscuit
