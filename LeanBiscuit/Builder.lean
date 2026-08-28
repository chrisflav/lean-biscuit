import LeanBiscuit.Datalog.World
import LeanBiscuit.Datalog.Print

/-!
# The builder layer

Datalog as written by a human, before interning: predicate names, strings and
public keys appear literally rather than as table indices.  This is what the
text parser produces, and what a program uses to describe the contents of a
block or an authorizer.

Converting to the interned representation is not merely a lookup: interning
assigns indices in traversal order, and a set is stored sorted by index, so the
order in which strings are first seen is observable in the printed form of a
set.  Converting back resolves the indices again.  Both directions are given
here so that a token's datalog can be moved between symbol tables — which is
exactly what an authorizer does when it loads a token's blocks.
-/

namespace LeanBiscuit
namespace Builder

open Datalog

/-- A map key, with its string spelled out. -/
inductive MapKey where
  /-- An integer key. -/
  | integer (value : Int)
  /-- A string key. -/
  | str (value : String)
  deriving Repr, Inhabited, DecidableEq

/-- A term, with its strings spelled out. -/
inductive Term where
  /-- A variable, named. -/
  | variable (name : String)
  /-- A signed 64 bit integer. -/
  | integer (value : Int)
  /-- A string. -/
  | str (value : String)
  /-- A date, in seconds since the Unix epoch. -/
  | date (value : Nat)
  /-- A byte string. -/
  | bytes (value : Bytes)
  /-- A boolean. -/
  | bool (value : Bool)
  /-- A set, sorted and deduplicated by the ordering below. -/
  | set (elements : List Term)
  /-- The absence of a value. -/
  | null
  /-- An array. -/
  | array (elements : List Term)
  /-- A map, sorted by key. -/
  | map (entries : List (MapKey × Term))
  deriving Repr, Inhabited

namespace MapKey

/-- Integers sort before strings; strings sort by their contents. -/
def compare : MapKey → MapKey → Ordering
  | .integer a, .integer b => Ord.compare a b
  | .integer _, .str _ => .lt
  | .str _, .integer _ => .gt
  | .str a, .str b => Ord.compare a b

end MapKey

namespace Term

/-- The constructor index, which is the primary sort key.  The gap at 7 is the
`Parameter` constructor of the reference implementation, which only exists for
its macro API and never appears in parsed source. -/
def tag : Term → Nat
  | .variable _ => 0
  | .integer _ => 1
  | .str _ => 2
  | .date _ => 3
  | .bytes _ => 4
  | .bool _ => 5
  | .set _ => 6
  | .null => 8
  | .array _ => 9
  | .map _ => 10

mutual

/-- Total ordering on builder terms.  Unlike the interned ordering, strings
compare by their contents; this is the order in which a set's elements are first
interned. -/
def compare : Term → Term → Ordering
  | .variable a, .variable b => Ord.compare a b
  | .integer a, .integer b => Ord.compare a b
  | .str a, .str b => Ord.compare a b
  | .date a, .date b => Ord.compare a b
  | .bytes a, .bytes b => Bytes.compare a b
  | .bool a, .bool b => Ord.compare (if a then 1 else 0) (if b then 1 else 0)
  | .set a, .set b => compareList a b
  | .null, .null => .eq
  | .array a, .array b => compareList a b
  | .map a, .map b => compareEntries a b
  | a, b => Ord.compare a.tag b.tag

/-- Lexicographic ordering of term lists. -/
def compareList : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a b with
    | .eq => compareList as bs
    | o => o

/-- Lexicographic ordering of map entry lists. -/
def compareEntries : List (MapKey × Term) → List (MapKey × Term) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (ka, va) :: as, (kb, vb) :: bs =>
    match MapKey.compare ka kb with
    | .eq => match compare va vb with
             | .eq => compareEntries as bs
             | o => o
    | o => o

end

end Term

/-- Insert into a sorted, deduplicated list of builder terms. -/
def sortedInsert (t : Term) : List Term → List Term
  | [] => [t]
  | x :: xs =>
    match Term.compare t x with
    | .lt => t :: x :: xs
    | .eq => x :: xs
    | .gt => x :: sortedInsert t xs

/-- The canonical form of a set. -/
def mkSet (l : List Term) : List Term := l.foldl (fun acc t => sortedInsert t acc) []

/-- Insert into a list of map entries kept sorted by key. -/
def entryInsert (k : MapKey) (v : Term) : List (MapKey × Term) → List (MapKey × Term)
  | [] => [(k, v)]
  | (k', v') :: xs =>
    match MapKey.compare k k' with
    | .lt => (k, v) :: (k', v') :: xs
    | .eq => (k, v) :: xs
    | .gt => (k', v') :: entryInsert k v xs

/-- The canonical form of a map. -/
def mkMap (l : List (MapKey × Term)) : List (MapKey × Term) :=
  l.foldl (fun acc (k, v) => entryInsert k v acc) []

/-- A unary opcode, with external function names spelled out. -/
inductive Unary where
  /-- Boolean negation. -/
  | negate
  /-- Explicit parentheses. -/
  | parens
  /-- Length. -/
  | length
  /-- Type name. -/
  | typeOf
  /-- A host function call. -/
  | ffi (name : String)
  deriving Repr, Inhabited, DecidableEq

/-- A binary opcode, with external function names spelled out. -/
inductive Binary where
  /-- `<`. -/
  | lessThan
  /-- `>`. -/
  | greaterThan
  /-- `<=`. -/
  | lessOrEqual
  /-- `>=`. -/
  | greaterOrEqual
  /-- `===`. -/
  | equal
  /-- `contains`. -/
  | contains
  /-- `starts_with`. -/
  | startsWith
  /-- `ends_with`. -/
  | endsWith
  /-- `matches`. -/
  | regex
  /-- `+`. -/
  | add
  /-- `-`. -/
  | sub
  /-- `*`. -/
  | mul
  /-- `/`. -/
  | div
  /-- Eager conjunction. -/
  | and
  /-- Eager disjunction. -/
  | or
  /-- `intersection`. -/
  | intersection
  /-- `union`. -/
  | union
  /-- `&`. -/
  | bitwiseAnd
  /-- `|`. -/
  | bitwiseOr
  /-- `^`. -/
  | bitwiseXor
  /-- `!==`. -/
  | notEqual
  /-- `==`. -/
  | heterogeneousEqual
  /-- `!=`. -/
  | heterogeneousNotEqual
  /-- `&&`. -/
  | lazyAnd
  /-- `||`. -/
  | lazyOr
  /-- `all`. -/
  | all
  /-- `any`. -/
  | any
  /-- `get`. -/
  | get
  /-- A host function call. -/
  | ffi (name : String)
  /-- `try_or`. -/
  | tryOr
  deriving Repr, Inhabited, DecidableEq

/-- A stack machine opcode, with names spelled out. -/
inductive Op where
  /-- Push a value. -/
  | value (term : Term)
  /-- Apply a unary operation. -/
  | unary (op : Unary)
  /-- Apply a binary operation. -/
  | binary (op : Binary)
  /-- Push a closure. -/
  | closure (params : List String) (ops : List Op)
  deriving Repr, Inhabited

/-- An expression. -/
structure Expression where
  /-- The opcodes. -/
  ops : List Op
  deriving Repr, Inhabited

/-- A predicate, named. -/
structure Predicate where
  /-- The predicate name. -/
  name : String
  /-- The arguments. -/
  terms : List Term
  deriving Repr, Inhabited

/-- A fact. -/
structure Fact where
  /-- The underlying predicate. -/
  predicate : Predicate
  deriving Repr, Inhabited

/-- A trust annotation, with public keys spelled out. -/
inductive Scope where
  /-- Trust the authority block. -/
  | authority
  /-- Trust all previous blocks. -/
  | previous
  /-- Trust blocks signed by this key. -/
  | publicKey (key : PublicKey)
  deriving Repr, Inhabited, DecidableEq

/-- A rule. -/
structure Rule where
  /-- The head. -/
  head : Predicate
  /-- The body predicates. -/
  body : List Predicate
  /-- The body expressions. -/
  expressions : List Expression
  /-- The trust annotation. -/
  scopes : List Scope
  deriving Repr, Inhabited

/-- A check. -/
structure Check where
  /-- The queries. -/
  queries : List Rule
  /-- The flavour of check. -/
  kind : CheckKind
  deriving Repr, Inhabited

/-- A policy. -/
structure Policy where
  /-- The queries. -/
  queries : List Rule
  /-- Whether it allows or denies. -/
  kind : PolicyKind
  deriving Repr, Inhabited

/-! ## Interning -/

/-! Interning a term is not merely a lookup: a set is stored sorted by index, so
the order in which its elements are first interned is observable in the printed
form.  The builder ordering above fixes that order. -/

mutual

/-- Intern a term's strings into `symbols`. -/
def Term.convert (symbols : SymbolTable) : Term → Datalog.Term × SymbolTable
  | .variable s => let (i, t) := symbols.insert s; (.variable i, t)
  | .integer i => (.integer i, symbols)
  | .str s => let (i, t) := symbols.insert s; (.str i, t)
  | .date d => (.date d, symbols)
  | .bytes b => (.bytes b, symbols)
  | .bool b => (.bool b, symbols)
  | .null => (.null, symbols)
  | .set l => let (terms, t) := Term.convertList symbols l; (.set (Datalog.mkSet terms), t)
  | .array l => let (terms, t) := Term.convertList symbols l; (.array terms, t)
  | .map entries =>
    let (es, t) := Term.convertEntries symbols entries
    (.map (Datalog.mkMap es), t)

/-- Intern each term of a list, in order. -/
def Term.convertList (symbols : SymbolTable) :
    List Term → List Datalog.Term × SymbolTable
  | [] => ([], symbols)
  | x :: xs =>
    let (x, symbols) := Term.convert symbols x
    let (xs, symbols) := Term.convertList symbols xs
    (x :: xs, symbols)

/-- Intern each entry of a map, in order. -/
def Term.convertEntries (symbols : SymbolTable) :
    List (MapKey × Term) → List (Datalog.MapKey × Datalog.Term) × SymbolTable
  | [] => ([], symbols)
  | (k, v) :: xs =>
    let (k, symbols) := match k with
      | .integer i => (Datalog.MapKey.integer i, symbols)
      | .str s => let (i, t) := symbols.insert s; (Datalog.MapKey.str i, t)
    let (v, symbols) := Term.convert symbols v
    let (xs, symbols) := Term.convertEntries symbols xs
    ((k, v) :: xs, symbols)

end

mutual

/-- Resolve a term's strings against `symbols`. -/
def Term.convertFrom (symbols : SymbolTable) : Datalog.Term → Except FormatError Term
  | .variable i => do pure (.variable (← symbols.get? i |>.getDM (throw (.unknownSymbol i))))
  | .integer i => pure (.integer i)
  | .str i => do pure (.str (← symbols.get? i |>.getDM (throw (.unknownSymbol i))))
  | .date d => pure (.date d)
  | .bytes b => pure (.bytes b)
  | .bool b => pure (.bool b)
  | .null => pure .null
  | .set l => do pure (.set (mkSet (← Term.convertFromList symbols l)))
  | .array l => do pure (.array (← Term.convertFromList symbols l))
  | .map entries => do pure (.map (mkMap (← Term.convertFromEntries symbols entries)))

/-- Resolve each term of a list. -/
def Term.convertFromList (symbols : SymbolTable) :
    List Datalog.Term → Except FormatError (List Term)
  | [] => pure []
  | x :: xs => do pure ((← Term.convertFrom symbols x) :: (← Term.convertFromList symbols xs))

/-- Resolve each entry of a map. -/
def Term.convertFromEntries (symbols : SymbolTable) :
    List (Datalog.MapKey × Datalog.Term) → Except FormatError (List (MapKey × Term))
  | [] => pure []
  | (k, v) :: xs => do
    let k ← match k with
      | .integer i => pure (MapKey.integer i)
      | .str i => do pure (MapKey.str (← symbols.get? i |>.getDM (throw (.unknownSymbol i))))
    pure ((k, ← Term.convertFrom symbols v) :: (← Term.convertFromEntries symbols xs))

end

/-- Intern a predicate. -/
def Predicate.convert (symbols : SymbolTable) (p : Predicate) :
    Datalog.Predicate × SymbolTable :=
  let (name, symbols) := symbols.insert p.name
  let (terms, symbols) := p.terms.foldl (fun (acc, t) x =>
    let (x, t) := Term.convert t x; (acc ++ [x], t)) (([] : List Datalog.Term), symbols)
  (⟨name, terms⟩, symbols)

/-- Resolve a predicate. -/
def Predicate.convertFrom (symbols : SymbolTable) (p : Datalog.Predicate) :
    Except FormatError Predicate := do
  let name ← symbols.get? p.name |>.getDM (throw (.unknownSymbol p.name))
  pure ⟨name, ← p.terms.mapM (Term.convertFrom symbols)⟩

/-- Intern a fact. -/
def Fact.convert (symbols : SymbolTable) (f : Fact) : Datalog.Fact × SymbolTable :=
  let (p, symbols) := f.predicate.convert symbols
  (⟨p⟩, symbols)

/-- Resolve a fact. -/
def Fact.convertFrom (symbols : SymbolTable) (f : Datalog.Fact) : Except FormatError Fact := do
  pure ⟨← Predicate.convertFrom symbols f.predicate⟩

/-- Intern a unary opcode. -/
def Unary.convert (symbols : SymbolTable) : Unary → Datalog.Unary × SymbolTable
  | .negate => (.negate, symbols)
  | .parens => (.parens, symbols)
  | .length => (.length, symbols)
  | .typeOf => (.typeOf, symbols)
  | .ffi n => let (i, t) := symbols.insert n; (.ffi i, t)

/-- Resolve a unary opcode. -/
def Unary.convertFrom (symbols : SymbolTable) : Datalog.Unary → Except FormatError Unary
  | .negate => pure .negate
  | .parens => pure .parens
  | .length => pure .length
  | .typeOf => pure .typeOf
  | .ffi i => do pure (.ffi (← symbols.get? i |>.getDM (throw (.unknownSymbol i))))

/-- Intern a binary opcode. -/
def Binary.convert (symbols : SymbolTable) : Binary → Datalog.Binary × SymbolTable
  | .lessThan => (.lessThan, symbols)
  | .greaterThan => (.greaterThan, symbols)
  | .lessOrEqual => (.lessOrEqual, symbols)
  | .greaterOrEqual => (.greaterOrEqual, symbols)
  | .equal => (.equal, symbols)
  | .contains => (.contains, symbols)
  | .startsWith => (.startsWith, symbols)
  | .endsWith => (.endsWith, symbols)
  | .regex => (.regex, symbols)
  | .add => (.add, symbols)
  | .sub => (.sub, symbols)
  | .mul => (.mul, symbols)
  | .div => (.div, symbols)
  | .and => (.and, symbols)
  | .or => (.or, symbols)
  | .intersection => (.intersection, symbols)
  | .union => (.union, symbols)
  | .bitwiseAnd => (.bitwiseAnd, symbols)
  | .bitwiseOr => (.bitwiseOr, symbols)
  | .bitwiseXor => (.bitwiseXor, symbols)
  | .notEqual => (.notEqual, symbols)
  | .heterogeneousEqual => (.heterogeneousEqual, symbols)
  | .heterogeneousNotEqual => (.heterogeneousNotEqual, symbols)
  | .lazyAnd => (.lazyAnd, symbols)
  | .lazyOr => (.lazyOr, symbols)
  | .all => (.all, symbols)
  | .any => (.any, symbols)
  | .get => (.get, symbols)
  | .tryOr => (.tryOr, symbols)
  | .ffi n => let (i, t) := symbols.insert n; (.ffi i, t)

/-- Resolve a binary opcode. -/
def Binary.convertFrom (symbols : SymbolTable) : Datalog.Binary → Except FormatError Binary
  | .lessThan => pure .lessThan
  | .greaterThan => pure .greaterThan
  | .lessOrEqual => pure .lessOrEqual
  | .greaterOrEqual => pure .greaterOrEqual
  | .equal => pure .equal
  | .contains => pure .contains
  | .startsWith => pure .startsWith
  | .endsWith => pure .endsWith
  | .regex => pure .regex
  | .add => pure .add
  | .sub => pure .sub
  | .mul => pure .mul
  | .div => pure .div
  | .and => pure .and
  | .or => pure .or
  | .intersection => pure .intersection
  | .union => pure .union
  | .bitwiseAnd => pure .bitwiseAnd
  | .bitwiseOr => pure .bitwiseOr
  | .bitwiseXor => pure .bitwiseXor
  | .notEqual => pure .notEqual
  | .heterogeneousEqual => pure .heterogeneousEqual
  | .heterogeneousNotEqual => pure .heterogeneousNotEqual
  | .lazyAnd => pure .lazyAnd
  | .lazyOr => pure .lazyOr
  | .all => pure .all
  | .any => pure .any
  | .get => pure .get
  | .tryOr => pure .tryOr
  | .ffi i => do pure (.ffi (← symbols.get? i |>.getDM (throw (.unknownSymbol i))))

mutual

/-- Intern an opcode. -/
def Op.convert (symbols : SymbolTable) : Op → Datalog.Op × SymbolTable
  | .value t => let (t, s) := Term.convert symbols t; (.value t, s)
  | .unary u => let (u, s) := Unary.convert symbols u; (.unary u, s)
  | .binary b => let (b, s) := Binary.convert symbols b; (.binary b, s)
  | .closure params ops =>
    let (ps, symbols) := params.foldl (fun (acc, t) p =>
      let (i, t) := t.insert p; (acc ++ [i], t)) (([] : List Nat), symbols)
    let (os, symbols) := Op.convertList symbols ops
    (.closure ps os, symbols)

/-- Intern each opcode of a sequence. -/
def Op.convertList (symbols : SymbolTable) : List Op → List Datalog.Op × SymbolTable
  | [] => ([], symbols)
  | x :: xs =>
    let (x, symbols) := Op.convert symbols x
    let (xs, symbols) := Op.convertList symbols xs
    (x :: xs, symbols)

end

mutual

/-- Resolve an opcode. -/
def Op.convertFrom (symbols : SymbolTable) : Datalog.Op → Except FormatError Op
  | .value t => do pure (.value (← Term.convertFrom symbols t))
  | .unary u => do pure (.unary (← Unary.convertFrom symbols u))
  | .binary b => do pure (.binary (← Binary.convertFrom symbols b))
  | .closure params ops => do
    let ps ← params.mapM fun p => symbols.get? p |>.getDM (throw (.unknownSymbol p))
    pure (.closure ps (← Op.convertFromList symbols ops))

/-- Resolve each opcode of a sequence. -/
def Op.convertFromList (symbols : SymbolTable) :
    List Datalog.Op → Except FormatError (List Op)
  | [] => pure []
  | x :: xs => do pure ((← Op.convertFrom symbols x) :: (← Op.convertFromList symbols xs))

end

/-- Intern an expression. -/
def Expression.convert (symbols : SymbolTable) (e : Expression) :
    Datalog.Expression × SymbolTable :=
  let (ops, symbols) := e.ops.foldl (fun (acc, t) o =>
    let (o, t) := Op.convert t o; (acc ++ [o], t)) (([] : List Datalog.Op), symbols)
  (⟨ops⟩, symbols)

/-- Resolve an expression. -/
def Expression.convertFrom (symbols : SymbolTable) (e : Datalog.Expression) :
    Except FormatError Expression := do
  pure ⟨← e.ops.mapM (Op.convertFrom symbols)⟩

/-- Intern a trust annotation, adding the key to the public key table. -/
def Scope.convert (symbols : SymbolTable) : Scope → Datalog.Scope × SymbolTable
  | .authority => (.authority, symbols)
  | .previous => (.previous, symbols)
  | .publicKey k => let (i, t) := symbols.insertKey k; (.publicKey i, t)

/-- Resolve a trust annotation. -/
def Scope.convertFrom (symbols : SymbolTable) : Datalog.Scope → Except FormatError Scope
  | .authority => pure .authority
  | .previous => pure .previous
  | .publicKey i =>
    match symbols.getKey? i with
    | some k => pure (.publicKey k)
    | none => throw .unknownExternalKey

/-- Intern a rule. -/
def Rule.convert (symbols : SymbolTable) (r : Rule) : Datalog.Rule × SymbolTable :=
  let (head, symbols) := r.head.convert symbols
  let (body, symbols) := r.body.foldl (fun (acc, t) p =>
    let (p, t) := Predicate.convert t p; (acc ++ [p], t)) (([] : List Datalog.Predicate), symbols)
  let (expressions, symbols) := r.expressions.foldl (fun (acc, t) e =>
    let (e, t) := Expression.convert t e; (acc ++ [e], t))
    (([] : List Datalog.Expression), symbols)
  let (scopes, symbols) := r.scopes.foldl (fun (acc, t) s =>
    let (s, t) := Scope.convert t s; (acc ++ [s], t)) (([] : List Datalog.Scope), symbols)
  (⟨head, body, expressions, scopes⟩, symbols)

/-- Resolve a rule. -/
def Rule.convertFrom (symbols : SymbolTable) (r : Datalog.Rule) : Except FormatError Rule := do
  pure ⟨← Predicate.convertFrom symbols r.head,
        ← r.body.mapM (Predicate.convertFrom symbols),
        ← r.expressions.mapM (Expression.convertFrom symbols),
        ← r.scopes.mapM (Scope.convertFrom symbols)⟩

/-- Intern a check. -/
def Check.convert (symbols : SymbolTable) (c : Check) : Datalog.Check × SymbolTable :=
  let (queries, symbols) := c.queries.foldl (fun (acc, t) q =>
    let (q, t) := Rule.convert t q; (acc ++ [q], t)) (([] : List Datalog.Rule), symbols)
  (⟨queries, c.kind⟩, symbols)

/-- Resolve a check. -/
def Check.convertFrom (symbols : SymbolTable) (c : Datalog.Check) : Except FormatError Check := do
  pure ⟨← c.queries.mapM (Rule.convertFrom symbols), c.kind⟩

/-- Intern a policy. -/
def Policy.convert (symbols : SymbolTable) (p : Policy) : Datalog.Policy × SymbolTable :=
  let (queries, symbols) := p.queries.foldl (fun (acc, t) q =>
    let (q, t) := Rule.convert t q; (acc ++ [q], t)) (([] : List Datalog.Rule), symbols)
  (⟨queries, p.kind⟩, symbols)

/-! ## Rendering

The reference implementation prints builder values directly from their strings,
except for expressions, which it renders by interning them into a fresh symbol
table and reusing the interned printer.  Both are reproduced here so that
authorizer policies read back exactly as they were written. -/

mutual

/-- Render a builder term. -/
def Term.print : Term → String
  | .variable v => s!"${v}"
  | .integer i => toString i
  | .str s => "\"" ++ s ++ "\""
  | .date d =>
    match Time.formatRfc3339 (if d ≥ 2 ^ 63 then (d : Int) - 2 ^ 64 else (d : Int)) with
    | some s => s
    | none => "<invalid date>"
  | .bytes b => s!"hex:{Bytes.toHex b}"
  | .bool b => if b then "true" else "false"
  | .set l =>
    if l.isEmpty then "{,}" else "{" ++ String.intercalate ", " (Term.printList l) ++ "}"
  | .null => "null"
  | .array l => "[" ++ String.intercalate ", " (Term.printList l) ++ "]"
  | .map entries => "{" ++ String.intercalate ", " (Term.printEntries entries) ++ "}"

/-- Render each term of a list. -/
def Term.printList : List Term → List String
  | [] => []
  | x :: xs => Term.print x :: Term.printList xs

/-- Render each entry of a map. -/
def Term.printEntries : List (MapKey × Term) → List String
  | [] => []
  | (k, v) :: xs =>
    (match k with
     | .integer i => s!"{i}: {Term.print v}"
     | .str s => "\"" ++ s ++ "\": " ++ Term.print v) :: Term.printEntries xs

end

/-- Render a builder predicate. -/
def Predicate.print (p : Predicate) : String :=
  p.name ++ "(" ++ String.intercalate ", " (p.terms.map Term.print) ++ ")"

/-- Render a builder trust annotation. -/
def Scope.print : Scope → String
  | .authority => "authority"
  | .previous => "previous"
  | .publicKey k => k.print

/-- Render a builder expression, by interning it into a fresh table. -/
def Expression.print (e : Expression) : String :=
  let (e, symbols) := Expression.convert {} e
  Datalog.printExpression symbols e

/-- Render the body of a builder rule. -/
def Rule.printBody (r : Rule) : String :=
  let preds := r.body.map Predicate.print
  let exprs := r.expressions.map Expression.print
  let e :=
    if exprs.isEmpty then ""
    else if preds.isEmpty then String.intercalate ", " exprs
    else ", " ++ String.intercalate ", " exprs
  let sc :=
    if r.scopes.isEmpty then ""
    else " trusting " ++ String.intercalate ", " (r.scopes.map Scope.print)
  String.intercalate ", " preds ++ e ++ sc

/-- Render a builder rule. -/
def Rule.print (r : Rule) : String := r.head.print ++ " <- " ++ r.printBody

/-- Render a builder check. -/
def Check.print (c : Check) : String :=
  let kind := match c.kind with
    | .one => "check if"
    | .all => "check all"
    | .reject => "reject if"
  kind ++ " " ++ String.intercalate " or " (c.queries.map Rule.printBody)

/-- Render a builder policy. -/
def Policy.print (p : Policy) : String :=
  let kind := match p.kind with
    | .allow => "allow"
    | .deny => "deny"
  if p.queries.isEmpty then kind
  else kind ++ " if " ++ String.intercalate " or " (p.queries.map Rule.printBody)

/-- Move a rule from one symbol table to another, as an authorizer does when it
loads a token's blocks. -/
def translateRule (source : SymbolTable) (target : SymbolTable) (r : Datalog.Rule) :
    Except FormatError (Datalog.Rule × SymbolTable) := do
  pure (Rule.convert target (← Rule.convertFrom source r))

end Builder
end LeanBiscuit
