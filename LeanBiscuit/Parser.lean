import LeanBiscuit.Builder
import LeanBiscuit.Util.Time

/-!
# Parsing datalog source

A recursive descent parser for the textual datalog of the specification.  The
token format itself is binary, but authorizers, blocks and policies are written
as text, so a complete implementation has to read it.

Alternatives backtrack: on failure the position is restored, which is what makes
the ambiguities of the grammar (a map versus a set, a predicate versus an
expression) resolvable by ordered choice.  Every loop is bounded by the length
of the input, so parsing is total.
-/

namespace LeanBiscuit
namespace Parser

open Builder Datalog

/-- The parser position within the input. -/
structure PState where
  /-- The characters being parsed. -/
  input : Array Char
  /-- The current offset. -/
  pos : Nat
  deriving Repr, Inhabited

/-- A backtracking parser: failure restores the position. -/
abbrev P (α : Type) := StateT PState (Except String) α

instance : Inhabited (P α) := ⟨fun _ => throw "unreachable"⟩

/-- Fail with a message. -/
def fail (message : String) : P α := fun _ => throw message

/-- Try `p`, falling back to `q` at the original position. -/
def orElse (p q : P α) : P α := fun s =>
  match p s with
  | .ok r => .ok r
  | .error _ => q s

instance : OrElse (P α) := ⟨fun p q => orElse p (q ())⟩

/-- Try the alternatives in order. -/
def choice (ps : List (P α)) : P α :=
  ps.foldr (fun p acc => orElse p acc) (fail "no alternative matched")

/-- Succeed with `none` instead of failing. -/
def opt (p : P α) : P (Option α) := (do pure (some (← p))) <|> pure none

/-- The character at the current position, if any. -/
def peek? : P (Option Char) := do
  let s ← get
  pure s.input[s.pos]?

/-- Are we at the end of the input? -/
def atEnd : P Bool := do
  let s ← get
  pure (s.pos ≥ s.input.size)

/-- Consume one character satisfying `p`. -/
def satisfy (p : Char → Bool) : P Char := do
  let s ← get
  match s.input[s.pos]? with
  | some c =>
    if p c then do set { s with pos := s.pos + 1 }; pure c
    else fail "unexpected character"
  | none => fail "unexpected end of input"

/-- Consume the given character. -/
def char (c : Char) : P Unit := do let _ ← satisfy (· == c); pure ()

/-- Consume the given literal. -/
def literal (t : String) : P Unit := do
  let s ← get
  let cs := t.toList
  let rec go (cs : List Char) (i : Nat) : Bool :=
    match cs with
    | [] => true
    | c :: rest => (s.input[i]? == some c) && go rest (i + 1)
  if go cs s.pos then set { s with pos := s.pos + cs.length }
  else fail s!"expected `{t}`"

/-- Consume characters while `p` holds. -/
def takeWhile (p : Char → Bool) : P String := do
  let s ← get
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel + 1 => match s.input[i]? with
      | some c => if p c then go (i + 1) fuel else i
      | none => i
  let stop := go s.pos (s.input.size - s.pos)
  set { s with pos := stop }
  pure (String.ofList (s.input.toList.drop s.pos |>.take (stop - s.pos)))

/-- Consume at least one character satisfying `p`. -/
def takeWhile1 (p : Char → Bool) : P String := do
  let r ← takeWhile p
  if r.isEmpty then fail "expected at least one character" else pure r

/-- Skip whitespace. -/
def ws : P Unit := do let _ ← takeWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

/-- Apply `p` as many times as it succeeds, requiring progress each time. -/
def many (p : P α) : Nat → P (List α)
  | 0 => pure []
  | fuel + 1 => fun s =>
    match p s with
    | .error _ => .ok ([], s)
    | .ok (a, s') =>
      if s'.pos > s.pos then
        match many p fuel s' with
        | .ok (rest, s'') => .ok (a :: rest, s'')
        | .error e => .error e
      else .ok ([a], s')

/-- One or more `p`, separated by `sep`. -/
def sepBy1 (p : P α) (sep : P Unit) (fuel : Nat) : P (List α) := do
  let first ← p
  let rest ← many (do sep; p) fuel
  pure (first :: rest)

/-- Zero or more `p`, separated by `sep`. -/
def sepBy (p : P α) (sep : P Unit) (fuel : Nat) : P (List α) :=
  sepBy1 p sep fuel <|> pure []

/-! ## Lexical elements -/

/-- Is `c` allowed in a name? -/
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == ':' || c.toNat > 127

/-- A predicate, variable or method name. -/
def name : P String := takeWhile1 isNameChar

/-- A quoted string, with `\\`, `\"` and `\n` escapes. -/
def stringLiteral : P String := do
  char '"'
  let rec go (acc : String) (fuel : Nat) : P String := do
    match fuel with
    | 0 => fail "unterminated string"
    | fuel + 1 =>
      match ← peek? with
      | none => fail "unterminated string"
      | some '"' => do char '"'; pure acc
      | some '\\' => do
        char '\\'
        match ← peek? with
        | some '\\' => do char '\\'; go (acc.push '\\') fuel
        | some '"' => do char '"'; go (acc.push '"') fuel
        | some 'n' => do char 'n'; go (acc.push '\n') fuel
        | _ => fail "invalid escape sequence"
      | some c => do let _ ← satisfy (fun _ => true); go (acc.push c) fuel
  let s ← get
  go "" (s.input.size - s.pos + 1)

/-- A decimal integer, possibly negative. -/
def integerLiteral : P Int := do
  let neg ← opt (char '-')
  let digits ← takeWhile1 Char.isDigit
  let n : Int := digits.toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat : Int)) 0
  pure (if neg.isSome then -n else n)

/-- A run of hexadecimal digits. -/
def hexLiteral : P Bytes := do
  let s ← takeWhile1 (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))
  match Bytes.ofHex? s with
  | some b => pure b
  | none => fail "invalid hexadecimal literal"

/-- An RFC 3339 timestamp. -/
def dateLiteral : P Nat := do
  let s ← takeWhile1 (fun c =>
    c != ',' && c != ' ' && c != ')' && c != ']' && c != ';' && c != '}' && c != '\n')
  match Time.parseRfc3339 s with
  | some t => if t < 0 then fail "dates before the epoch are not representable"
              else pure t.toNat
  | none => fail "invalid date"

/-- A public key, as `ed25519/…` or `secp256r1/…`. -/
def publicKeyLiteral : P PublicKey :=
  (do literal "ed25519/"; let b ← hexLiteral
      if b.size != 32 then fail "invalid Ed25519 public key" else pure ⟨.ed25519, b⟩) <|>
  (do literal "secp256r1/"; let b ← hexLiteral
      if b.size != 33 then fail "invalid secp256r1 public key" else pure ⟨.secp256r1, b⟩)

/-! ## Terms -/

/-- Which terms are admissible in a position. -/
inductive TermContext where
  /-- Inside a rule: variables are allowed. -/
  | rule
  /-- Inside a fact: no variables. -/
  | fact
  /-- Inside a set: no variables, no sets, no arrays. -/
  | set
  deriving Repr, DecidableEq

/-- `true` or `false`. -/
def boolLiteral : P Builder.Term :=
  (do literal "true"; pure (.bool true)) <|> (do literal "false"; pure (.bool false))

/-- `null`. -/
def nullLiteral : P Builder.Term := do literal "null"; pure .null

/-! Nesting a term inside a set, array or map costs at least one bracket, so the
length of the input bounds the nesting depth; `fuel` carries that bound. -/

mutual

/-- Parse a term in the given context. -/
def term (ctx : TermContext) (fuel : Nat) : P Builder.Term := do
  ws
  match fuel with
  | 0 => fail "term is nested too deeply"
  | fuel + 1 =>
    match ctx with
    | .rule => choice [
        (do pure (.str (← stringLiteral))),
        (do pure (.date (← dateLiteral))),
        (do char '$'; pure (.variable (← name))),
        (do pure (.integer (← integerLiteral))),
        (do literal "hex:"; pure (.bytes (← hexLiteral))),
        boolLiteral, nullLiteral, arrayLiteral fuel, mapLiteral fuel, setLiteral fuel]
    | .fact => choice [
        (do pure (.str (← stringLiteral))),
        (do pure (.date (← dateLiteral))),
        (do pure (.integer (← integerLiteral))),
        (do literal "hex:"; pure (.bytes (← hexLiteral))),
        boolLiteral, nullLiteral, setLiteral fuel, arrayLiteral fuel, mapLiteral fuel]
    | .set => choice [
        (do pure (.str (← stringLiteral))),
        (do pure (.date (← dateLiteral))),
        (do pure (.integer (← integerLiteral))),
        (do literal "hex:"; pure (.bytes (← hexLiteral))),
        boolLiteral, nullLiteral, mapLiteral fuel]
termination_by (fuel, 0)

/-- A set literal; `{,}` is the empty set. -/
def setLiteral (fuel : Nat) : P Builder.Term :=
  (do literal "{,}"; pure (.set [])) <|>
  (do
    ws; char '{'
    let s ← get
    let elements ← sepBy1 (term .set fuel) (do ws; char ',') (s.input.size - s.pos + 1)
    ws; char '}'
    if elements.any (fun t => match t with | .variable _ => true | _ => false) then
      fail "variables are not permitted in sets"
    if elements.any (fun t => match t with | .set _ => true | _ => false) then
      fail "sets cannot contain other sets"
    -- a set's elements must all have the same type
    match elements.map (·.tag) with
    | [] => pure (.set [])
    | t :: rest =>
      if rest.all (· == t) then pure (.set (mkSet elements))
      else fail "set elements must have the same type")
termination_by (fuel, 1)

/-- An array literal. -/
def arrayLiteral (fuel : Nat) : P Builder.Term := do
  ws; char '['
  let s ← get
  let elements ← sepBy (term .fact fuel) (do ws; char ',') (s.input.size - s.pos + 1)
  ws; char ']'
  pure (.array elements)
termination_by (fuel, 1)

/-- A map literal. -/
def mapLiteral (fuel : Nat) : P Builder.Term := do
  ws; char '{'
  let s ← get
  let entries ← sepBy (do
    ws
    let k ← (do pure (Builder.MapKey.str (← stringLiteral)))
            <|> (do pure (Builder.MapKey.integer (← integerLiteral)))
    ws; char ':'
    pure (k, ← term .fact fuel)) (do ws; char ',') (s.input.size - s.pos + 1)
  ws; char '}'
  pure (.map (mkMap entries))
termination_by (fuel, 1)

end

/-! ## Expressions -/

/-- The binary operators at each precedence level, loosest first. -/
def levelOperators : Nat → List (String × Builder.Binary)
  | 0 => [("||", .lazyOr)]
  | 1 => [("&&", .lazyAnd)]
  | 2 => [("<=", .lessOrEqual), (">=", .greaterOrEqual), ("<", .lessThan), (">", .greaterThan),
          ("===", .equal), ("!==", .notEqual), ("==", .heterogeneousEqual),
          ("!=", .heterogeneousNotEqual)]
  | 3 => [("^", .bitwiseXor)]
  | 4 => [("|", .bitwiseOr)]
  | 5 => [("&", .bitwiseAnd)]
  | 6 => [("+", .add), ("-", .sub)]
  | 7 => [("*", .mul), ("/", .div)]
  | _ => []

/-- Parse one of the operators of a level. -/
def levelOperator (lvl : Nat) : P Builder.Binary := do
  ws
  choice ((levelOperators lvl).map fun (t, op) => do literal t; pure op)

/-- The two-argument methods, and whether they take a closure parameter. -/
def binaryMethods : List (String × Builder.Binary) :=
  [("contains", .contains), ("starts_with", .startsWith), ("ends_with", .endsWith),
   ("matches", .regex), ("intersection", .intersection), ("union", .union),
   ("all", .all), ("any", .any), ("get", .get), ("try_or", .tryOr)]

/-- The zero-argument methods. -/
def unaryMethods : List (String × Builder.Unary) := [("length", .length), ("type", .typeOf)]

/-- An expression tree, before it is flattened to opcodes. -/
inductive Expr where
  /-- A leaf value. -/
  | value (term : Builder.Term)
  /-- A unary application. -/
  | unary (op : Builder.Unary) (e : Expr)
  /-- A binary application. -/
  | binary (op : Builder.Binary) (l r : Expr)
  /-- A closure, with its parameters. -/
  | closure (params : List String) (body : Expr)
  deriving Repr, Inhabited

namespace Expr

/-- Flatten an expression tree into the opcode sequence the stack machine
runs. -/
def toOps : Expr → List Builder.Op
  | .value t => [.value t]
  | .unary op e => toOps e ++ [.unary op]
  | .binary op l r => toOps l ++ toOps r ++ [.binary op]
  | .closure params body => [.closure params (toOps body)]

end Expr

mutual

/-- Parse an expression. -/
def expr (fuel : Nat) : P Expr := level fuel 0
termination_by (fuel, 4, 0)

/-- Parse the operators of precedence level `lvl` and everything tighter. -/
def level (fuel : Nat) (lvl : Nat) : P Expr := do
  if lvl ≥ 8 then unaryLevel fuel
  else
    let first ← level fuel (lvl + 1)
    if lvl == 2 then
      -- comparisons do not associate: at most one operator
      match ← opt (do let op ← levelOperator lvl; pure (op, ← level fuel (lvl + 1))) with
      | none => pure first
      | some (op, second) => pure (.binary op first second)
    else
      let s ← get
      let rest ← many (do
        let op ← levelOperator lvl
        pure (op, ← level fuel (lvl + 1))) (s.input.size - s.pos + 1)
      -- the short-circuiting operators take their right operand as a closure
      pure (rest.foldl (fun acc (op, e) =>
        match op with
        | .lazyAnd | .lazyOr => .binary op acc (.closure [] e)
        | _ => .binary op acc e) first)
termination_by (fuel, 3, 8 - lvl)

/-- Parse a prefix negation, or fall through to method calls. -/
def unaryLevel (fuel : Nat) : P Expr :=
  match fuel with
  | 0 => fail "expression is nested too deeply"
  | fuel + 1 =>
    (do ws; char '!'; ws; pure (.unary .negate (← level fuel 6))) <|> methodLevel (fuel + 1)
termination_by (fuel, 2, 0)

/-- Parse an atom followed by any number of method calls. -/
def methodLevel (fuel : Nat) : P Expr := do
  let initial ← atom fuel
  methodLoop fuel initial
termination_by (fuel, 1, 0)

/-- Parse the chain of method calls applied to `initial`. -/
def methodLoop (fuel : Nat) (initial : Expr) : P Expr :=
  match fuel with
  | 0 => pure initial
  | fuel + 1 =>
    (do
      char '.'
      let next ←
        (do
          let op ← choice ((binaryMethods.map fun (n, op) => do literal n; pure op)
                            ++ [do literal "extern::"; pure (Builder.Binary.ffi (← name))])
          char '('
          ws
          match op with
          | .all | .any => do
            char '$'
            let param ← name
            ws; literal "->"; ws
            let arg ← expr fuel
            ws; char ')'
            pure (Expr.binary op initial (.closure [param] arg))
          | .tryOr => do
            let arg ← expr fuel
            ws; char ')'
            pure (Expr.binary op (.closure [] initial) arg)
          | _ => do
            let arg ← expr fuel
            ws; char ')'
            pure (Expr.binary op initial arg)) <|>
        (do
          let op ← choice ((unaryMethods.map fun (n, op) => do literal n; pure op)
                            ++ [do literal "extern::"; pure (Builder.Unary.ffi (← name))])
          char '('; ws; char ')'
          pure (Expr.unary op initial))
      methodLoop fuel next) <|> pure initial
termination_by (fuel, 0, 0)

/-- Parse a parenthesised expression or a term. -/
def atom (fuel : Nat) : P Expr :=
  match fuel with
  | 0 => fail "expression is nested too deeply"
  | fuel + 1 =>
    (do ws; char '('; ws; let e ← expr fuel; ws; char ')'; pure (.unary .parens e)) <|>
    (do pure (.value (← term .rule (fuel + 1))))
termination_by (fuel, 0, 1)

end

/-! ## Statements -/

/-- Parse a predicate. -/
def predicate : P Builder.Predicate := do
  ws
  let n ← name
  ws
  char '('
  let s ← get
  let terms ← sepBy1 (term .rule (s.input.size + 1)) (do ws; char ',')
    (s.input.size - s.pos + 1)
  ws
  char ')'
  pure ⟨n, terms⟩

/-- Parse a rule head, which unlike a predicate may take no arguments. -/
def ruleHead : P Builder.Predicate := do
  ws
  let n ← name
  ws
  char '('
  let s ← get
  let terms ← sepBy (term .rule (s.input.size + 1)) (do ws; char ',')
    (s.input.size - s.pos + 1)
  ws
  char ')'
  pure ⟨n, terms⟩

/-- Parse a fact, which may not contain variables. -/
def fact : P Builder.Fact := do
  ws
  let n ← name
  ws
  char '('
  let s ← get
  let terms ← sepBy1 (term .fact (s.input.size + 1)) (do ws; char ',')
    (s.input.size - s.pos + 1)
  ws
  char ')'
  pure ⟨⟨n, terms⟩⟩

/-- Parse a trust annotation. -/
def scopes : P (List Builder.Scope) :=
  (do
    ws
    literal "trusting"
    let s ← get
    sepBy1 (do
      ws
      choice [ (do literal "authority"; pure Builder.Scope.authority),
               (do literal "previous"; pure Builder.Scope.previous),
               (do pure (Builder.Scope.publicKey (← publicKeyLiteral))) ])
      (do ws; char ',') (s.input.size - s.pos + 1)) <|> pure []

/-- Parse the body of a rule: predicates and expressions, then trust. -/
def ruleBody : P (List Builder.Predicate × List Builder.Expression × List Builder.Scope) := do
  let s ← get
  let fuel := s.input.size * 2 + 16
  let elements ← sepBy1
    (do ws; (do pure (Sum.inl (← predicate))) <|> (do pure (Sum.inr (← expr fuel))))
    (do ws; char ',') (s.input.size - s.pos + 1)
  let sc ← scopes
  let predicates := elements.filterMap fun | .inl p => some p | _ => none
  let expressions := elements.filterMap fun
    | .inr e => some (Builder.Expression.mk e.toOps)
    | _ => none
  pure (predicates, expressions, sc)

/-- Parse a rule, rejecting one whose head has a variable the body does not
bind: such a rule could conjure facts out of nothing. -/
def rule : P Builder.Rule := do
  let head ← ruleHead
  ws
  literal "<-"
  let (body, expressions, sc) ← ruleBody
  let r : Builder.Rule := ⟨head, body, expressions, sc⟩
  let bodyVars := body.flatMap fun p => p.terms.filterMap fun
    | .variable v => some v
    | _ => none
  let unbound := head.terms.filterMap fun
    | .variable v => if bodyVars.contains v then none else some v
    | _ => none
  if !unbound.isEmpty then
    fail ("rule head contains variables that are not used in predicates of the rule's body: "
      ++ String.intercalate ", " (unbound.map ("$" ++ ·)))
  pure r

/-- Parse the queries of a check or policy, separated by `or`. -/
def checkBody : P (List Builder.Rule) := do
  let s ← get
  sepBy1 (do
    ws
    let (body, expressions, sc) ← ruleBody
    pure (⟨⟨"query", []⟩, body, expressions, sc⟩ : Builder.Rule))
    (do ws; literal "or") (s.input.size - s.pos + 1)

/-- Parse a check. -/
def check : P Builder.Check := do
  ws
  let kind ← choice [
    (do literal "check if"; pure CheckKind.one),
    (do literal "check all"; pure CheckKind.all),
    (do literal "reject if"; pure CheckKind.reject)]
  pure ⟨← checkBody, kind⟩

/-- Parse an allow or deny policy. -/
def policy : P Builder.Policy := do
  ws
  let kind ← choice [
    (do literal "allow if"; pure PolicyKind.allow),
    (do literal "deny if"; pure PolicyKind.deny)]
  pure ⟨← checkBody, kind⟩

/-- Skip a line or block comment. -/
def comment : P Unit :=
  (do
    ws; literal "//"
    let _ ← takeWhile (fun c => c != '\n' && c != '\r')
    let _ ← opt (literal "\n")) <|>
  (do
    ws; literal "/*"
    let s ← get
    let rec go (fuel : Nat) : P Unit := do
      match fuel with
      | 0 => fail "unterminated comment"
      | fuel + 1 => (do literal "*/") <|> (do let _ ← satisfy (fun _ => true); go fuel)
    go (s.input.size - s.pos + 1))

/-- The end of a statement. -/
def statementEnd : P Unit := do
  ws
  (do char ';') <|> (do if ← atEnd then pure () else fail "expected `;`")

/-- The result of parsing a source file. -/
structure Source where
  /-- The block-level trust annotation, if any. -/
  scopes : List Builder.Scope := []
  /-- The facts stated. -/
  facts : List Builder.Fact := []
  /-- The rules defined. -/
  rules : List Builder.Rule := []
  /-- The checks imposed. -/
  checks : List Builder.Check := []
  /-- The policies, which only an authorizer may carry. -/
  policies : List Builder.Policy := []
  deriving Repr, Inhabited

/-- One statement of a source file. -/
inductive Statement where
  /-- A fact. -/
  | fact (value : Builder.Fact)
  /-- A rule. -/
  | rule (value : Builder.Rule)
  /-- A check. -/
  | check (value : Builder.Check)
  /-- A policy. -/
  | policy (value : Builder.Policy)
  /-- A comment, which contributes nothing. -/
  | comment
  deriving Repr, Inhabited

/-- Parse one statement.

Rules are tried before facts because a rule's head looks exactly like a fact
until the arrow is reached. -/
def statement : P Statement :=
  choice [
    (do let r ← rule; statementEnd; pure (.rule r)),
    (do let f ← fact; statementEnd; pure (.fact f)),
    (do let c ← check; statementEnd; pure (.check c)),
    (do let p ← policy; statementEnd; pure (.policy p)),
    (do comment; pure .comment)]

/-- Parse a whole source file. -/
def sourceFile (allowBlockScopes : Bool) : P Source := do
  let mut result : Source := {}
  if allowBlockScopes then
    match ← opt (do let sc ← scopes; if sc.isEmpty then fail "no scopes" else do
                    statementEnd; pure sc) with
    | some sc => result := { result with scopes := sc }
    | none => pure ()
  let s ← get
  let statements ← many (do ws; if ← atEnd then fail "end of input" else statement)
    (s.input.size + 1)
  ws
  if !(← atEnd) then
    let s ← get
    fail s!"unexpected trailing data at offset {s.pos}"
  for st in statements do
    match st with
    | .fact f => result := { result with facts := result.facts ++ [f] }
    | .rule r => result := { result with rules := result.rules ++ [r] }
    | .check c => result := { result with checks := result.checks ++ [c] }
    | .policy p => result := { result with policies := result.policies ++ [p] }
    | .comment => pure ()
  pure result

/-- Parse authorizer source: facts, rules, checks and policies. -/
def parseAuthorizer (source : String) : Except String Source :=
  (sourceFile false).run' ⟨source.toList.toArray, 0⟩

/-- Parse block source: like authorizer source, but with an optional block-level
trust annotation and no policies. -/
def parseBlock (source : String) : Except String Source := do
  let r ← (sourceFile true).run' ⟨source.toList.toArray, 0⟩
  if !r.policies.isEmpty then throw "a block cannot contain policies"
  pure r

end Parser
end LeanBiscuit
